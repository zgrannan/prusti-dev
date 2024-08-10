use pcs::{combined_pcs::BodyWithBorrowckFacts, utils::Place};
use prusti_rustc_interface::{
    abi::FIRST_VARIANT,
    ast,
    ast::Local,
    hir::Mutability,
    index::IndexVec,
    middle::{
        mir::{self, PlaceElem, VarDebugInfo},
        ty::{self, GenericArgsRef},
    },
    span::def_id::DefId,
    type_ir::sty::TyKind,
};
use std::{
    collections::{BTreeSet, HashMap},
    marker::PhantomData,
};
use symbolic_execution::{
    context::SymExContext,
    heap::HeapData,
    path_conditions::PathConditions,
    results::ResultPath,
    semantics::VerifierSemantics,
    terminator::{FunctionCallEffects, FunctionCallResult},
    value::{AggregateKind, Substs, SymValue, SymValueData, SyntheticSymValue, Ty},
    visualization::{OutputMode, VisFormat},
    SymExParams, SymbolicExecution,
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
// TODO: replace uses of `CapabilityEnc` with `SnapshotEnc`
use crate::{
    debug::fn_debug_name,
    encoders::{CapabilityEnc, ConstEnc, MirBuiltinEnc, SnapshotEnc, ViperTupleEnc},
};

use super::{mir_base::MirBaseEnc, mir_pure::PureKind};

pub struct SymPureEnc;

#[derive(Clone, Debug)]
pub enum SymPureEncError {
    UnsupportedStatement,
    UnsupportedTerminator,
}

// TODO: does this need to be `&'vir [..]`?
type ExprInput<'vir> = (DefId, &'vir [vir::Expr<'vir>]);
type ExprRet<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone, Debug)]
pub struct SymPureEncOutput<'sym, 'tcx> {
    pub expr: PrustiSymValue<'sym, 'tcx>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymPureEncTask<'tcx> {
    pub kind: PureKind,
    pub parent_def_id: DefId,             // ID of the function
    pub param_env: ty::ParamEnv<'tcx>,    // param environment at the usage site
    pub substs: ty::GenericArgsRef<'tcx>, // type substitutions at the usage site
    pub caller_def_id: Option<DefId>,     // Caller/Use DefID
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymPureEncResult<'sym, 'tcx> {
    paths: BTreeSet<(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)>,
    pub debug_id: Option<String>,
}

impl<'sym, 'tcx> SymPureEncResult<'sym, 'tcx> {
    pub fn from_sym_value(value: PrustiSymValue<'sym, 'tcx>) -> Self {
        Self {
            paths: vec![(PathConditions::new(), value)].into_iter().collect(),
            debug_id: None,
        }
    }

    pub fn into_iter(
        self,
    ) -> impl Iterator<Item = (PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.paths.into_iter()
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = &(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.paths.iter()
    }

    pub fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'sym PrustiSubsts<'sym, 'tcx>,
    ) -> Self {
        let mut result = BTreeSet::new();
        for (path_conditions, value) in self.paths {
            let path_conditions = path_conditions.subst(arena, substs);
            let value = value.subst(arena, substs);
            result.insert((path_conditions, value));
        }
        Self {
            paths: result,
            debug_id: self.debug_id,
        }
    }
}

pub struct PrustiSemantics<'sym, 'tcx>(pub PhantomData<&'sym &'tcx ()>);

pub type PrustiSymValSynthetic<'sym, 'tcx> = &'sym PrustiSymValSyntheticData<'sym, 'tcx>;

#[derive(Ord, Eq, Debug, PartialEq, PartialOrd, Clone)]
pub enum PrustiSymValSyntheticData<'sym, 'tcx> {
    And(PrustiSymValue<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>),
    If(
        PrustiSymValue<'sym, 'tcx>,
        PrustiSymValue<'sym, 'tcx>,
        PrustiSymValue<'sym, 'tcx>,
    ),
    PureFnCall(
        DefId,
        GenericArgsRef<'tcx>,
        &'sym [PrustiSymValue<'sym, 'tcx>],
    ),
    Result(ty::Ty<'tcx>),
    VirLocal(&'sym str, ty::Ty<'tcx>),
    Old(mir::Local, Vec<PlaceElem<'tcx>>, ty::Ty<'tcx>),
}

impl<'sym, 'tcx> VisFormat for &'sym PrustiSymValSyntheticData<'sym, 'tcx> {
    fn to_vis_string(
        &self,
        tcx: Option<ty::TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match self {
            PrustiSymValSyntheticData::And(l, r) => format!(
                "({} && {})",
                l.to_vis_string(tcx, debug_info, mode),
                r.to_vis_string(tcx, debug_info, mode)
            ),
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => format!(
                "({} ? {} : {})",
                cond.to_vis_string(tcx, debug_info, mode),
                then_expr.to_vis_string(tcx, debug_info, mode),
                else_expr.to_vis_string(tcx, debug_info, mode)
            ),
            PrustiSymValSyntheticData::PureFnCall(def_id, substs, args) => vir::with_vcx(|vcx| {
                let fn_name = vcx.tcx().item_name(*def_id);
                let args_str = args
                    .iter()
                    .map(|arg| arg.to_vis_string(tcx, debug_info, mode))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", fn_name, args_str)
            }),
            PrustiSymValSyntheticData::Result(ty) => "result".to_string(),
            PrustiSymValSyntheticData::VirLocal(name, _) => name.to_string(),
            PrustiSymValSyntheticData::Old(local, projection, _) => {
                format!("old({:?}{:?})", local, projection)
            }
        }
    }
}

impl<'sym, 'tcx> std::fmt::Display for PrustiSymValSyntheticData<'sym, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            PrustiSymValSyntheticData::And(_, _) => todo!(),
            PrustiSymValSyntheticData::If(_, _, _) => todo!(),
            PrustiSymValSyntheticData::PureFnCall(def_id, _, args) => {
                let fn_name = format!("{:?}", def_id);
                let args_str = args
                    .iter()
                    .map(|arg| format!("{}", arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}({})", fn_name, args_str)
            }
            PrustiSymValSyntheticData::Result(_) => todo!(),
            PrustiSymValSyntheticData::VirLocal(_, _) => todo!(),
            PrustiSymValSyntheticData::Old(_, _, _) => todo!(),
        }
    }
}

impl<'sym, 'tcx> SyntheticSymValue<'sym, 'tcx> for PrustiSymValSynthetic<'sym, 'tcx> {
    fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        substs: &Substs<'sym, 'tcx, Self>,
    ) -> Self {
        match self {
            PrustiSymValSyntheticData::And(l, r) => arena.alloc(PrustiSymValSyntheticData::And(
                l.subst(arena, substs),
                r.subst(arena, substs),
            )),
            PrustiSymValSyntheticData::PureFnCall(def_id, ty_substs, args) => {
                arena.alloc(PrustiSymValSyntheticData::PureFnCall(
                    *def_id,
                    ty_substs,
                    arena.alloc_slice(
                        &(args
                            .iter()
                            .map(|arg| arg.subst(arena, substs))
                            .collect::<Vec<_>>()),
                    ),
                ))
            }
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => {
                arena.alloc(PrustiSymValSyntheticData::If(
                    cond.subst(arena, substs),
                    then_expr.subst(arena, substs),
                    else_expr.subst(arena, substs),
                ))
            }
            PrustiSymValSyntheticData::Result(_) => todo!(),
            PrustiSymValSyntheticData::VirLocal(_, _) => todo!(),
            PrustiSymValSyntheticData::Old(_, _, _) => self,
        }
    }

    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match &self {
            PrustiSymValSyntheticData::And(_, _) => Ty::new(tcx.types.bool, None),
            PrustiSymValSyntheticData::If(_, t, _) => t.ty(tcx),
            PrustiSymValSyntheticData::PureFnCall(def_id, substs, _) => Ty::new(
                tcx.fn_sig(def_id)
                    .instantiate(tcx, substs)
                    .output()
                    .skip_binder(),
                None,
            ),
            PrustiSymValSyntheticData::Result(ty) => Ty::new(*ty, None),
            PrustiSymValSyntheticData::VirLocal(_, ty) => Ty::new(*ty, None),
            PrustiSymValSyntheticData::Old(local, projection, ty) => Ty::new(*ty, None),
        }
    }

    fn optimize(self, arena: &'sym SymExContext<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Self {
        match &self {
            PrustiSymValSyntheticData::And(lhs, rhs) => arena.alloc(
                PrustiSymValSyntheticData::And(lhs.optimize(arena, tcx), rhs.optimize(arena, tcx)),
            ),
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => {
                arena.alloc(PrustiSymValSyntheticData::If(
                    cond.optimize(arena, tcx),
                    then_expr.optimize(arena, tcx),
                    else_expr.optimize(arena, tcx),
                ))
            }
            PrustiSymValSyntheticData::PureFnCall(def_id, ty_substs, args) => {
                arena.alloc(PrustiSymValSyntheticData::PureFnCall(
                    *def_id,
                    ty_substs,
                    arena.alloc_slice(
                        &(args
                            .iter()
                            .map(|arg| arg.optimize(arena, tcx))
                            .collect::<Vec<_>>()),
                    ),
                ))
            }
            PrustiSymValSyntheticData::Result(_) => self,
            PrustiSymValSyntheticData::VirLocal(_, _) => self,
            PrustiSymValSyntheticData::Old(_, _, _) => self,
        }
    }
}

pub type PrustiPathConditions<'sym, 'tcx> =
    PathConditions<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSymValue<'sym, 'tcx> = SymValue<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSubsts<'sym, 'tcx> = Substs<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

impl<'sym, 'tcx> VerifierSemantics<'sym, 'tcx> for PrustiSemantics<'sym, 'tcx> {
    type SymValSynthetic = PrustiSymValSynthetic<'sym, 'tcx>;

    fn encode_fn_call<'mir>(
        location: mir::Location,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        args: &Vec<mir::Operand<'tcx>>,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic>> {
        vir::with_vcx(|vcx| {
            let fn_name = vcx.tcx().def_path_str(def_id);
            if fn_name == "prusti_contracts::old" {
                // if !matches!(
                //     args[0].ty(sym_ex.body, vcx.tcx()).ref_mutability(),
                //     Some(Mutability::Mut)
                // ) {
                //     return Some(FunctionCallEffects {
                //         precondition_assertion: None,
                //         result: FunctionCallResult::Value {
                //             value: sym_ex.encode_operand(heap, &args[0]),
                //             postcondition: None,
                //         },
                //         snapshot: None,
                //     });
                // }
                match args[0] {
                    mir::Operand::Move(place) => {
                        match &sym_ex.body.basic_blocks[location.block].statements
                            [location.statement_index - 1]
                            .kind
                        {
                            mir::StatementKind::Assign(box (left, e)) => {
                                assert!(left.local == place.local);
                                assert!(left.projection == place.projection);
                                let value = match e {
                                    mir::Rvalue::Use(
                                        mir::Operand::Copy(place) | mir::Operand::Move(place),
                                    ) => sym_ex.arena.mk_synthetic(sym_ex.arena.alloc(
                                        PrustiSymValSyntheticData::Old(
                                            place.local,
                                            place.projection.to_vec(),
                                            place.ty(sym_ex.body, vcx.tcx()).ty,
                                        ),
                                    )),
                                    mir::Rvalue::Ref(_, _, place) => {
                                        let e = sym_ex.arena.mk_synthetic(sym_ex.arena.alloc(
                                            PrustiSymValSyntheticData::Old(
                                                place.local,
                                                place.projection.to_vec(),
                                                place.ty(sym_ex.body, vcx.tcx()).ty,
                                            ),
                                        ));
                                        sym_ex.arena.mk_ref(e, Mutability::Not)
                                    }
                                    _ => todo!(),
                                };
                                return Some(FunctionCallEffects {
                                    result: FunctionCallResult::Value {
                                        value,
                                        postcondition: None,
                                    },
                                    precondition_assertion: None,
                                    snapshot: None,
                                });
                            }
                            kind => todo!("For {place:?} kind {kind:?}"),
                        }
                    }
                    // mir::Operand::Constant(c) => sym_ex.arena.mk_constant(c.into()),
                    _ => todo!(),
                }
            }
            let args: Vec<_> = args
                .iter()
                .map(|arg| sym_ex.encode_operand(heap, arg))
                .collect();
            let args = sym_ex.arena.alloc_slice(&args);
            match fn_name.as_str() {
                "prusti_contracts::before_expiry" => {
                    return Some(FunctionCallEffects {
                        precondition_assertion: None,
                        result: FunctionCallResult::Value {
                            value: args[0],
                            postcondition: None,
                        },
                        snapshot: None,
                    });
                }
                "std::boxed::Box::<T>::new" => {
                    assert_eq!(args.len(), 1);
                    let output_ty = vcx
                        .tcx()
                        .fn_sig(def_id)
                        .instantiate(vcx.tcx(), substs)
                        .output()
                        .skip_binder();
                    let substs = if let ty::TyKind::Adt(_, substs) = output_ty.kind() {
                        substs
                    } else {
                        unreachable!()
                    };
                    return Some(FunctionCallEffects {
                        precondition_assertion: None,
                        result: FunctionCallResult::Value {
                            value: sym_ex.arena.mk_aggregate(
                                AggregateKind::Rust(
                                    mir::AggregateKind::Adt(
                                        vcx.tcx().lang_items().owned_box().unwrap(),
                                        FIRST_VARIANT,
                                        substs,
                                        None,
                                        None,
                                    ),
                                    output_ty,
                                ),
                                args,
                            ),
                            postcondition: None,
                        },
                        snapshot: None,
                    });
                }
                _ => {}
            }

            let is_pure = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                proc_spec.kind.is_pure().unwrap_or_default()
            })
            .unwrap_or(
                fn_name == "std::cmp::PartialEq::eq" || fn_name == "std::cmp::PartialEq::ne",
            );
            if is_pure {
                return Some(FunctionCallEffects {
                    precondition_assertion: None,
                    result: FunctionCallResult::Value {
                        value: sym_ex.arena.mk_synthetic(
                            sym_ex
                                .arena
                                .alloc(PrustiSymValSyntheticData::PureFnCall(def_id, substs, args)),
                        ),
                        postcondition: None,
                    },
                    snapshot: None,
                });
            } else {
                return None;
            }
        })
    }
}

impl SymPureEnc {
    pub fn encode<'sym, 'tcx>(
        arena: &'sym SymExContext<'tcx>,
        task: SymPureEncTask<'tcx>,
        debug_output_dir: Option<String>,
    ) -> SymPureEncResult<'sym, 'tcx> {
        let kind = task.kind;
        let def_id = task.parent_def_id;
        let substs = task.substs;
        let caller_def_id = task.caller_def_id;
        vir::with_vcx(move |vcx| {
            let body = match kind {
                PureKind::Closure => vcx
                    .body_mut()
                    .get_closure_body(def_id, substs, caller_def_id),
                PureKind::Spec => vcx.body_mut().get_spec_body(def_id, substs, caller_def_id),
                PureKind::Pure => vcx
                    .body_mut()
                    .get_pure_fn_body(def_id, substs, caller_def_id),
                PureKind::Constant(promoted) => todo!(),
            };
            let body = body.body().as_ref().clone();
            let arg_count = body.body.arg_count;
            let symbolic_execution = symbolic_execution::run_symbolic_execution(SymExParams {
                def_id: def_id.as_local().unwrap(),
                body: &body.body,
                tcx: vcx.tcx(),
                fpcs_analysis: pcs::run_free_pcs(
                    &BodyWithBorrowckFacts {
                        body: body.body.clone(),
                        promoted: body.promoted,
                        borrow_set: body.borrow_set,
                        region_inference_context: body.region_inference_context,
                        location_table: body.location_table,
                        input_facts: body.input_facts,
                        output_facts: body.output_facts,
                    },
                    vcx.tcx(),
                    debug_output_dir.clone(),
                ),
                verifier_semantics: PrustiSemantics(PhantomData),
                arena: &arena,
                debug_output_dir: debug_output_dir.clone(),
                new_symvars_allowed: false,
            });
            assert_eq!(
                symbolic_execution.symvars.len(),
                arg_count,
                "The symvars for pure {:?} don't correspond to its arguments",
                def_id
            );
            SymPureEncResult {
                paths: symbolic_execution
                    .paths
                    .into_iter()
                    .map(|path| (path.pcs, path.result))
                    .collect(),
                debug_id: Some(fn_debug_name(def_id, substs)),
            }
        })
    }
}
