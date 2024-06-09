use mir_state_analysis::symbolic_execution::{
    path_conditions::PathConditions,
    value::{Substs, SymValue, SymValueData, SyntheticSymValueData, Ty},
    ResultPath, SymExArena, VerifierSemantics,
};
use prusti_rustc_interface::{
    ast,
    ast::Local,
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
    type_ir::sty::TyKind,
};
use std::{
    collections::{BTreeSet, HashMap},
    marker::PhantomData,
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

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = &(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.0.iter()
    }

    pub fn subst(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &PrustiSubsts<'sym, 'tcx>,
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

pub struct PrustiSemantics<'tcx>(pub PhantomData<&'tcx ()>);

#[derive(Ord, Eq, Debug, PartialEq, PartialOrd, Clone)]
pub enum PrustiSymValSynthetic<'sym, 'tcx> {
    And(PrustiSymValue<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>),
    If(
        PrustiSymValue<'sym, 'tcx>,
        PrustiSymValue<'sym, 'tcx>,
        PrustiSymValue<'sym, 'tcx>,
    ),
    PureFnCall(DefId, &'sym [PrustiSymValue<'sym, 'tcx>]),
}

impl<'sym, 'tcx> SyntheticSymValueData<'sym, 'tcx> for PrustiSymValSynthetic<'sym, 'tcx> {
    fn subst(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'sym Substs<'sym, 'tcx, Self>,
    ) -> Self {
        match self {
            PrustiSymValSynthetic::And(l, r) => {
                PrustiSymValSynthetic::And(l.subst(arena, tcx, substs), r.subst(arena, tcx, substs))
            }
            PrustiSymValSynthetic::PureFnCall(def_id, args) => PrustiSymValSynthetic::PureFnCall(
                def_id,
                arena.alloc_slice(
                    &args
                        .into_iter()
                        .map(|arg| arg.subst(arena, tcx, substs))
                        .collect(),
                ),
            ),
            PrustiSymValSynthetic::If(cond, then_expr, else_expr) => PrustiSymValSynthetic::If(
                cond.subst(arena, tcx, substs),
                then_expr.subst(arena, tcx, substs),
                else_expr.subst(arena, tcx, substs),
            ),
        }
    }

    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match &self {
            PrustiSymValSynthetic::And(_, _) => Ty::new(tcx.types.bool, None),
            PrustiSymValSynthetic::If(_, t, _) => t.ty(tcx),
            PrustiSymValSynthetic::PureFnCall(def_id, _) => Ty::new(
                tcx.fn_sig(def_id).skip_binder().output().skip_binder(),
                None,
            ),
        }
    }
}

pub type PrustiPathConditions<'sym, 'tcx> =
    PathConditions<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSymValue<'sym, 'tcx> = SymValue<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSubsts<'sym, 'tcx> = Substs<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

impl<'sym, 'tcx> VerifierSemantics<'sym, 'tcx> for PrustiSemantics<'tcx> {
    type SymValSynthetic = PrustiSymValSynthetic<'sym, 'tcx>;

    fn encode_fn_call(
        arena: &'sym SymExArena,
        def_id: DefId,
        args: &[&PrustiSymValue<'sym, 'tcx>],
    ) -> Option<PrustiSymValue<'sym, 'tcx>> {
        let is_pure = crate::encoders::with_proc_spec(def_id, |proc_spec| {
            proc_spec.kind.is_pure().unwrap_or_default()
        })
        .unwrap_or_default();
        if is_pure {
            Some(arena.alloc(SymValueData::Synthetic(
                arena.alloc(PrustiSymValSynthetic::PureFnCall(def_id, args)),
            )))
        } else {
            None
        }
    }
}

impl SymPureEnc {
    pub fn encode<'sym, 'tcx>(
        arena: &'sym SymExArena,
        task: SymPureEncTask<'tcx>,
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
            let body = &*body.body();
            let symbolic_execution = mir_state_analysis::run_symbolic_execution(
                body,
                vcx.tcx(),
                mir_state_analysis::run_free_pcs(body, vcx.tcx()),
                PrustiSemantics(PhantomData),
                arena
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
