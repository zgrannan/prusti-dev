use pcs::combined_pcs::BodyWithBorrowckFacts;
use prusti_rustc_interface::{
    abi::FIRST_VARIANT,
    ast,
    ast::Local,
    index::IndexVec,
    middle::{
        mir::VarDebugInfo,
        ty::{self, GenericArgsRef},
    },
    span::def_id::DefId,
    type_ir::sty::TyKind,
};
use rustc_middle::mir;
use std::{
    collections::{BTreeSet, HashMap},
    marker::PhantomData,
};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::PathConditions,
    results::ResultPath,
    semantics::VerifierSemantics,
    value::{AggregateKind, Substs, SymValue, SymValueData, SyntheticSymValue, Ty},
    visualization::VisFormat,
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
// TODO: replace uses of `CapabilityEnc` with `SnapshotEnc`
use crate::encoders::{CapabilityEnc, ConstEnc, MirBuiltinEnc, SnapshotEnc, ViperTupleEnc};

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
pub struct SymPureEncResult<'sym, 'tcx>(
    BTreeSet<(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)>,
);

impl<'sym, 'tcx> SymPureEncResult<'sym, 'tcx> {
    pub fn from_sym_value(value: PrustiSymValue<'sym, 'tcx>) -> Self {
        Self(vec![(PathConditions::new(), value)].into_iter().collect())
    }

    pub fn into_iter(
        self,
    ) -> impl Iterator<Item = (PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.0.into_iter()
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = &(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.0.iter()
    }

    pub fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'sym PrustiSubsts<'sym, 'tcx>,
    ) -> Self {
        let mut result = BTreeSet::new();
        for (path_conditions, value) in self.0 {
            let path_conditions = path_conditions.subst(arena, tcx, substs);
            let value = value.subst(arena, tcx, substs);
            result.insert((path_conditions, value));
        }
        Self(result)
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
}

impl<'sym, 'tcx> VisFormat for &'sym PrustiSymValSyntheticData<'sym, 'tcx> {
    fn to_vis_string(&self, debug_info: &[VarDebugInfo]) -> String {
        match self {
            PrustiSymValSyntheticData::And(l, r) => format!(
                "({} && {})",
                l.to_vis_string(debug_info),
                r.to_vis_string(debug_info)
            ),
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => format!(
                "({} ? {} : {})",
                cond.to_vis_string(debug_info),
                then_expr.to_vis_string(debug_info),
                else_expr.to_vis_string(debug_info)
            ),
            PrustiSymValSyntheticData::PureFnCall(def_id, substs, args) => vir::with_vcx(|vcx| {
                let fn_name = vcx.tcx().item_name(*def_id);
                let args_str = args
                    .iter()
                    .map(|arg| arg.to_vis_string(debug_info))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", fn_name, args_str)
            }),
            PrustiSymValSyntheticData::Result(ty) => "result".to_string(),
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
                l.subst(arena, tcx, substs),
                r.subst(arena, tcx, substs),
            )),
            PrustiSymValSyntheticData::PureFnCall(def_id, ty_substs, args) => {
                arena.alloc(PrustiSymValSyntheticData::PureFnCall(
                    *def_id,
                    ty_substs,
                    arena.alloc_slice(
                        &(args
                            .iter()
                            .map(|arg| {
                                eprintln!("subst arg: {} {:?}", arg, substs);
                                arg.subst(arena, tcx, substs)
                            })
                            .collect::<Vec<_>>()),
                    ),
                ))
            }
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => {
                arena.alloc(PrustiSymValSyntheticData::If(
                    cond.subst(arena, tcx, substs),
                    then_expr.subst(arena, tcx, substs),
                    else_expr.subst(arena, tcx, substs),
                ))
            }
            PrustiSymValSyntheticData::Result(_) => todo!(),
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
        }
    }
}

pub type PrustiPathConditions<'sym, 'tcx> =
    PathConditions<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSymValue<'sym, 'tcx> = SymValue<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSubsts<'sym, 'tcx> = Substs<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

impl<'sym, 'tcx> VerifierSemantics<'sym, 'tcx> for PrustiSemantics<'sym, 'tcx> {
    type SymValSynthetic = PrustiSymValSynthetic<'sym, 'tcx>;

    fn encode_fn_call(
        &self,
        arena: &'sym SymExContext<'tcx>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: &'sym [PrustiSymValue<'sym, 'tcx>],
    ) -> Option<PrustiSymValue<'sym, 'tcx>> {
        vir::with_vcx(|vcx| {
            let fn_name = vcx.tcx().def_path_str(def_id);
            if fn_name == "std::boxed::Box::<T>::new" {
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
                return Some(arena.mk_aggregate(
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
                ));
            }

            let is_pure = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                proc_spec.kind.is_pure().unwrap_or_default()
            })
            .unwrap_or(
                fn_name == "std::cmp::PartialEq::eq" || fn_name == "std::cmp::PartialEq::ne",
            );
            if is_pure {
                Some(arena.mk_synthetic(
                    arena.alloc(PrustiSymValSyntheticData::PureFnCall(def_id, substs, args)),
                ))
            } else {
                None
            }
        })
    }
}

impl SymPureEnc {
    pub fn encode<'sym, 'tcx>(
        arena: &'sym SymExContext<'tcx>,
        task: SymPureEncTask<'tcx>,
        debug_output_dir: Option<&str>,
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
            let symbolic_execution = symbolic_execution::run_symbolic_execution(
                def_id.as_local().unwrap(),
                &body.body.clone(),
                vcx.tcx(),
                pcs::run_free_pcs(
                    &BodyWithBorrowckFacts {
                        body: body.body,
                        promoted: body.promoted,
                        borrow_set: body.borrow_set,
                        region_inference_context: body.region_inference_context,
                        location_table: body.location_table,
                        input_facts: body.input_facts,
                        output_facts: body.output_facts,
                    },
                    vcx.tcx(),
                    debug_output_dir,
                ),
                PrustiSemantics(PhantomData),
                arena,
                debug_output_dir,
            );
            assert_eq!(
                symbolic_execution.symvars.len(),
                arg_count,
                "The symvars for pure {:?} don't correspond to its arguments",
                def_id
            );
            SymPureEncResult(
                symbolic_execution
                    .paths
                    .into_iter()
                    .map(|(_, path_conditions, value)| (path_conditions, value))
                    .collect(),
            )
        })
    }
}
