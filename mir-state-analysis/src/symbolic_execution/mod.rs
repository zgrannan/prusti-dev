pub mod place;
pub mod heap;
pub mod value;
pub mod path;
pub mod path_conditions;

use crate::{
    coupling_graph::BodyWithBorrowckFacts,
    havoc::HavocData,
    symbolic_execution::{heap::SymbolicHeap, value::SymValueData},
};
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir,
        ty::{self, GenericArgsRef, TyCtxt},
    },
};
use std::{collections::BTreeSet, ops::Deref, rc::Rc};

use crate::FpcsOutput;

use self::{
    path::{AcyclicPath, Path},
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    place::Place,
    value::{AggregateKind, SymValue, SyntheticSymValueData},
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Assertion<'sym, 'tcx, T> {
    Eq(SymValue<'sym, 'tcx, T>, bool),
    Precondition(DefId, GenericArgsRef<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
}

pub type ResultPath<'sym, 'tcx, T> = (
    AcyclicPath,
    PathConditions<'sym, 'tcx, T>,
    SymValueData<'sym, 'tcx, T>,
);
pub type ResultAssertion<'sym, 'tcx, T> = (
    AcyclicPath,
    PathConditions<'sym, 'tcx, T>,
    Assertion<'sym, 'tcx, T>,
);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicExecutionResult<'sym, 'tcx, T> {
    pub paths: BTreeSet<ResultPath<'sym, 'tcx, T>>,
    pub assertions: BTreeSet<ResultAssertion<'sym, 'tcx, T>>,
    pub symvars: Vec<ty::Ty<'tcx>>,
}

pub struct SymExArena {
    bump: bumpalo::Bump,
}

impl SymExArena {
    pub fn new() -> Self {
        Self {
            bump: bumpalo::Bump::new(),
        }
    }
    pub fn alloc<T>(&self, t: T) -> &T {
        self.bump.alloc(t)
    }
    pub fn alloc_slice<T: Copy>(&self, t: &[T]) -> &[T] {
        self.bump.alloc_slice_copy(t)
    }
}

pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    tcx: TyCtxt<'tcx>,
    body: &'mir BodyWithBorrowckFacts<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: HavocData,
    symvars: Vec<ty::Ty<'tcx>>,
    arena: &'sym SymExArena,
    verifier_semantics: S,
}

pub trait VerifierSemantics<'sym, 'tcx> {
    type SymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValueData<'sym, 'tcx>;
    fn encode_fn_call(
        def_id: DefId,
        args: &[SymValue<'sym, 'tcx, Self::SymValSynthetic>],
    ) -> Option<SymValue<'sym, 'tcx, Self::SymValSynthetic>>;
}

impl<'mir: 'sym, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> SymbolicExecution<'mir, 'sym, 'tcx, S> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir BodyWithBorrowckFacts<'tcx>,
        fpcs_analysis: FpcsOutput<'mir, 'tcx>,
        verifier_semantics: S,
        arena: &'sym SymExArena,
    ) -> Self {
        SymbolicExecution {
            tcx,
            body,
            fpcs_analysis,
            havoc: HavocData::new(&body.body),
            symvars: Vec::with_capacity(body.body.arg_count),
            verifier_semantics,
            arena,
        }
    }

    fn handle_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        paths: &mut Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
        assertions: &mut BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>>,
        result_paths: &mut BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>>,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
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
                            path.heap.encode_operand(self.arena, discr),
                            pred.clone(),
                        ));
                        paths.push(path);
                    }
                }
                if let Some(mut path) = path.push_if_acyclic(targets.otherwise()) {
                    let pred =
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                    path.pcs.insert(PathConditionAtom::new(
                        path.heap.encode_operand(self.arena, discr),
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
                let cond = path.heap.encode_operand(self.arena, cond);
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
                ty::TyKind::FnDef(def_id, substs) => {
                    let args: Vec<_> = args
                        .iter()
                        .map(|arg| path.heap.encode_operand(self.arena, arg))
                        .collect();

                    let args: &'sym [SymValue<'sym, 'tcx, S::SymValSynthetic>] =
                        self.alloc_slice(&args);

                    assertions.insert((
                        path.path.clone(),
                        path.pcs.clone(),
                        Assertion::Precondition(*def_id, substs, args),
                    ));

                    let result = S::encode_fn_call(*def_id, args).unwrap_or_else(|| {
                        self.mk_fresh_symvar(
                            destination.ty(&self.body.body.local_decls, self.tcx).ty,
                        )
                    });
                    path.heap.insert((*destination).into(), result);
                    path.pcs.insert(PathConditionAtom::new(
                        result,
                        PathConditionPredicate::Postcondition(*def_id, substs, args),
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

    pub fn execute(&mut self) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        let mut result_paths: BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut init_heap = SymbolicHeap::new();
        for (idx, arg) in self.body.body.args_iter().enumerate() {
            let local = &self.body.body.local_decls[arg];
            let arg_ty = local.ty;
            self.symvars.push(arg_ty);
            let place = Place::new(arg, Vec::new());
            init_heap.insert(place, self.alloc(SymValueData::Var(idx, arg_ty)));
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
        path: &Path<'sym, 'tcx, S::SymValSynthetic>,
        result_paths: &mut BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>>,
    ) {
        if let Some(expr) = path.heap.get_return_place_expr() {
            result_paths.insert((path.path.clone(), path.pcs.clone(), expr.clone()));
        }
    }

    fn handle_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut SymbolicHeap<'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                let sym_value = match rvalue {
                    mir::Rvalue::Use(operand) => heap.encode_operand(self.arena, &operand),
                    mir::Rvalue::CheckedBinaryOp(op, box (lhs, rhs)) => {
                        let lhs = heap.encode_operand(self.arena, &lhs);
                        let rhs = heap.encode_operand(self.arena, &rhs);
                        self.alloc(SymValueData::CheckedBinaryOp(
                            place.ty(&self.body.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        ))
                    }
                    mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                        let lhs = heap.encode_operand(self.arena, &lhs);
                        let rhs = heap.encode_operand(self.arena, &rhs);
                        self.alloc(SymValueData::BinaryOp(
                            place.ty(&self.body.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        ))
                    }
                    mir::Rvalue::Aggregate(kind, ops) => {
                        let ops = ops
                            .iter()
                            .map(|op| heap.encode_operand(self.arena, op))
                            .collect::<Vec<_>>();
                        self.alloc(SymValueData::Aggregate(
                            AggregateKind::from_mir(
                                *kind.clone(),
                                place.ty(&self.body.body.local_decls, self.tcx).ty,
                            ),
                            self.alloc_slice(&ops),
                        ))
                    }
                    mir::Rvalue::Discriminant(target) => self.alloc(SymValueData::Discriminant(
                        heap.get(&(*target).into()).unwrap(),
                    )),
                    mir::Rvalue::Ref(_, _, place) => {
                        self.alloc(SymValueData::Ref(heap.get(&(*place).into()).unwrap()))
                    }
                    mir::Rvalue::UnaryOp(op, operand) => {
                        let operand = heap.encode_operand(self.arena, operand);
                        self.alloc(SymValueData::UnaryOp(
                            place.ty(&self.body.body.local_decls, self.tcx).ty,
                            *op,
                            operand,
                        ))
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

    fn mk_fresh_symvar(&mut self, ty: ty::Ty<'tcx>) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        let var = self.alloc(SymValueData::Var(self.symvars.len(), ty));
        self.symvars.push(ty);
        var
    }

    fn handle_repacks(
        &self,
        repacks: &Vec<crate::free_pcs::RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for repack in repacks {
            self.handle_repack(repack, heap)
        }
    }

    fn alloc<T>(&self, t: T) -> &'sym T {
        self.arena.alloc(t)
    }
    fn alloc_slice<T: Copy>(&self, t: &[T]) -> &'sym [T] {
        self.arena.alloc_slice(t)
    }

    fn handle_repack(
        &self,
        repack: &crate::free_pcs::RepackOp<'tcx>,
        heap: &mut SymbolicHeap<'sym, 'tcx, S::SymValSynthetic>,
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
                    let mut value = value;
                    for elem in f.projection.iter().skip(old_proj_len) {
                        value = self.alloc(SymValueData::Projection(elem.clone(), value));
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
                    self.alloc(SymValueData::Aggregate(
                        AggregateKind::new(
                            place_ty.ty,
                            from.ty(self.fpcs_analysis.repacker()).variant_index,
                        ),
                        self.arena.alloc_slice(&places),
                    )),
                );
            }
            crate::free_pcs::RepackOp::DerefShallowInit(_, _) => todo!(),
        }
    }
}
