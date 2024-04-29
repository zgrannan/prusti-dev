pub mod place;
pub mod heap;
pub mod value;
pub mod path;
pub mod path_conditions;

use crate::{
    coupling_graph::BodyWithBorrowckFacts,
    havoc::HavocData,
    symbolic_execution::{heap::SymbolicHeap, value::SymValue},
    BasicBlock,
};
use prusti_rustc_interface::{
    abi::FIRST_VARIANT,
    dataflow::{
        fmt::DebugWithContext, Analysis, AnalysisDomain, JoinSemiLattice, SwitchIntEdgeEffects,
    },
    hir::def_id::DefId,
    middle::{
        mir::{self, Body},
        ty::{self, TyCtxt},
    },
};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Deref,
};

use crate::{
    free_pcs::{FreePcsBasicBlock, FreePcsLocation, FreePcsTerminator},
    FpcsOutput,
};

use self::{
    path::{AcyclicPath, Path}, path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions}, place::Place, value::AggregateKind
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Assertion<'tcx> {
    Eq(SymValue<'tcx>, bool),
    Precondition(DefId, Vec<SymValue<'tcx>>),
}

pub type ResultPath<'tcx> = (AcyclicPath, PathConditions<'tcx>, SymValue<'tcx>);
pub type ResultAssertion<'tcx> = (AcyclicPath, PathConditions<'tcx>, Assertion<'tcx>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicExecutionResult<'tcx> {
    pub paths: BTreeSet<ResultPath<'tcx>>,
    pub assertions: BTreeSet<ResultAssertion<'tcx>>,
    pub symvars: Vec<ty::Ty<'tcx>>,
}

pub struct SymbolicExecution<'mir, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'mir BodyWithBorrowckFacts<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: HavocData,
    symvars: Vec<ty::Ty<'tcx>>,
}

impl<'mir, 'tcx> SymbolicExecution<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir BodyWithBorrowckFacts<'tcx>,
        fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    ) -> Self {
        SymbolicExecution {
            tcx,
            body,
            fpcs_analysis,
            havoc: HavocData::new(&body.body),
            symvars: Vec::with_capacity(body.body.arg_count),
        }
    }

    fn handle_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        paths: &mut Vec<Path<'tcx>>,
        assertions: &mut BTreeSet<ResultAssertion<'tcx>>,
        result_paths: &mut BTreeSet<ResultPath<'tcx>>,
        path: &mut Path<'tcx>,
    ) {
        match &terminator.kind {
            mir::TerminatorKind::Drop { target, .. }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::Goto { target } => {
                if let Some(path) = path.push_if_acyclic(*target) {
                    paths.push(path);
                }
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let ty = discr.ty(&self.body.body.local_decls, self.tcx);
                for (value, target) in targets.iter() {
                    let pred = PathConditionPredicate::Eq(value, ty);
                    if let Some(mut path) = path.push_if_acyclic(target) {
                        path.pcs.insert(PathConditionAtom::new(
                            path.heap.encode_operand(discr),
                            pred.clone(),
                        ));
                        paths.push(path);
                    }
                }
                if let Some(mut path) = path.push_if_acyclic(targets.otherwise()) {
                    let pred =
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                    path.pcs.insert(PathConditionAtom::new(
                        path.heap.encode_operand(discr),
                        pred.clone(),
                    ));
                    paths.push(path);
                }
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let cond = path.heap.encode_operand(cond);
                assertions.insert((
                    path.path.clone(),
                    path.pcs.clone(),
                    Assertion::Eq(cond, *expected),
                ));
                if let Some(path) = path.push_if_acyclic(*target) {
                    paths.push(path);
                }
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => match func.ty(&self.body.body.local_decls, self.tcx).kind() {
                ty::TyKind::FnDef(def_id, _) => {
                    let args: Vec<SymValue<'_>> = args
                        .iter()
                        .map(|arg| path.heap.encode_operand(arg))
                        .collect();
                    assertions.insert((
                        path.path.clone(),
                        path.pcs.clone(),
                        Assertion::Precondition(*def_id, args.clone()),
                    ));
                    let sym_var = self
                        .mk_fresh_symvar(destination.ty(&self.body.body.local_decls, self.tcx).ty);
                    path.heap.insert((*destination).into(), sym_var.clone());
                    path.pcs.insert(PathConditionAtom::new(
                        sym_var,
                        PathConditionPredicate::Postcondition(*def_id, args),
                    ));
                    if let Some(target) = target {
                        if let Some(path) = path.push_if_acyclic(*target) {
                            paths.push(path);
                        }
                    }
                }
                _ => panic!(),
            },
            mir::TerminatorKind::Unreachable | mir::TerminatorKind::Return { .. } => {}
            other => {
                todo!("other terminator {:#?}", other)
            }
        }
        if terminator.successors().next().is_none() {
            self.add_to_result_paths_if_feasible(&path, result_paths);
        }
    }

    pub fn execute(&mut self) -> SymbolicExecutionResult<'tcx> {
        let mut result_paths: BTreeSet<ResultPath<'tcx>> = BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'tcx>> = BTreeSet::new();
        let mut init_heap = SymbolicHeap::new();
        for (idx, arg) in self.body.body.args_iter().enumerate() {
            let local = &self.body.body.local_decls[arg];
            let arg_ty = local.ty;
            self.symvars.push(arg_ty);
            let place = Place::new(arg, Vec::new());
            init_heap.insert(place, SymValue::Var(idx, arg_ty));
        }
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            init_heap,
        )];
        while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            for local in self.havoc.get(block).iter() {
                path.heap.insert(
                    (*local).into(),
                    self.mk_fresh_symvar(self.body.body.local_decls[*local].ty),
                );
            }
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.body.basic_blocks[block];
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                let fpcs_loc = &pcs_block.statements[stmt_idx];
                self.handle_repacks(&fpcs_loc.repacks_start, &mut path.heap);
                self.handle_stmt(stmt, &mut path.heap);
            }
            let last_fpcs_loc = pcs_block.statements.last().unwrap();
            self.handle_repacks(&last_fpcs_loc.repacks_start, &mut path.heap);
            if let Some(terminator) = &block_data.terminator {
                self.handle_terminator(
                    terminator,
                    &mut paths,
                    &mut assertions,
                    &mut result_paths,
                    &mut path,
                );
            } else {
                self.add_to_result_paths_if_feasible(&path, &mut result_paths);
            }
        }
        SymbolicExecutionResult {
            paths: result_paths,
            assertions,
            symvars: self.symvars.clone(),
        }
    }

    fn add_to_result_paths_if_feasible(
        &mut self,
        path: &Path<'tcx>,
        result_paths: &mut BTreeSet<ResultPath<'tcx>>,
    ) {
        if let Some(expr) = path.heap.get_return_place_expr() {
            result_paths.insert((path.path.clone(), path.pcs.clone(), expr.clone()));
        }
    }

    fn handle_stmt(&mut self, stmt: &mir::Statement<'tcx>, heap: &mut SymbolicHeap<'tcx>) {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                let sym_value = match rvalue {
                    mir::Rvalue::Use(operand) => heap.encode_operand(&operand),
                    mir::Rvalue::CheckedBinaryOp(op, box (lhs, rhs)) => {
                        let lhs = heap.encode_operand(&lhs);
                        let rhs = heap.encode_operand(&rhs);
                        SymValue::CheckedBinaryOp(
                            place.ty(&self.body.body.local_decls, self.tcx).ty,
                            *op,
                            Box::new(lhs),
                            Box::new(rhs),
                        )
                    }
                    mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                        let lhs = heap.encode_operand(&lhs);
                        let rhs = heap.encode_operand(&rhs);
                        SymValue::BinaryOp(
                            place.ty(&self.body.body.local_decls, self.tcx).ty,
                            *op,
                            Box::new(lhs),
                            Box::new(rhs),
                        )
                    }
                    mir::Rvalue::Aggregate(kind, ops) => {
                        let ops = ops.iter().map(|op| heap.encode_operand(op)).collect();
                        SymValue::Aggregate(
                            AggregateKind::from_mir(
                                *kind.clone(),
                                place.ty(&self.body.body.local_decls, self.tcx).ty,
                            ),
                            ops,
                        )
                    }
                    mir::Rvalue::Discriminant(target) => SymValue::Discriminant(Box::new(
                        heap.get(&(*target).into()).unwrap().clone(),
                    )),
                    mir::Rvalue::Ref(_, _, place) => {
                        SymValue::Ref(Box::new(heap.get(&(*place).into()).unwrap().clone()))
                    }
                    _ => todo!("{rvalue:?}"),
                };
                heap.insert((*place).into(), sym_value);
            }
            mir::StatementKind::StorageDead(_)
            | mir::StatementKind::StorageLive(_)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::AscribeUserType(..) => {}
            other => todo!("{:?}", other),
        }
    }

    fn mk_fresh_symvar(&mut self, ty: ty::Ty<'tcx>) -> SymValue<'tcx> {
        let var = SymValue::Var(self.symvars.len(), ty);
        self.symvars.push(ty);
        var
    }

    fn handle_repacks(
        &self,
        repacks: &Vec<crate::free_pcs::RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'tcx>,
    ) {
        for repack in repacks {
            self.handle_repack(repack, heap)
        }
    }

    fn handle_repack(
        &self,
        repack: &crate::free_pcs::RepackOp<'tcx>,
        heap: &mut SymbolicHeap<'tcx>,
    ) {
        match repack {
            crate::free_pcs::RepackOp::StorageDead(_) => todo!(),
            crate::free_pcs::RepackOp::IgnoreStorageDead(_) => todo!(),
            crate::free_pcs::RepackOp::Weaken(_, _, _) => todo!(),
            crate::free_pcs::RepackOp::Expand(place, guide, _) => {
                let value = heap.take(&place.deref().into());
                let old_proj_len = place.projection.len();
                let (field, rest, _) =
                    place.expand_one_level(*guide, self.fpcs_analysis.repacker());
                for f in std::iter::once(&field).chain(rest.iter()) {
                    let mut value = value.clone();
                    for elem in f.projection.iter().skip(old_proj_len) {
                        value = SymValue::Projection(elem.clone(), Box::new(value.clone()));
                    }
                    heap.insert(f.deref().into(), value)
                }
            }
            crate::free_pcs::RepackOp::Collapse(place, from, _) => {
                let places: Vec<_> = place
                    .expand_field(None, self.fpcs_analysis.repacker())
                    .iter()
                    .map(|p| heap.take(&p.deref().into()))
                    .collect();

                let place_ty = place.ty(self.fpcs_analysis.repacker());
                heap.insert(
                    place.deref().into(),
                    SymValue::Aggregate(
                        AggregateKind::new(
                            place_ty.ty,
                            from.ty(self.fpcs_analysis.repacker()).variant_index,
                        ),
                        places,
                    ),
                );
            }
            crate::free_pcs::RepackOp::DerefShallowInit(_, _) => todo!(),
        }
    }
}
