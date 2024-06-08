use mir_state_analysis::symbolic_execution::{
    path_conditions::PathConditions, value::{Substs, SymValue}, VerifierSemantics, ResultPath
};
use prusti_rustc_interface::{
    ast,
    ast::Local,
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
    type_ir::sty::TyKind,
};
use std::collections::{BTreeSet, HashMap};
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
pub struct SymPureEncOutput<'vir> {
    pub expr: PrustiSymValue<'vir>,
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
pub struct SymPureEncResult<'tcx>(BTreeSet<(PrustiPathConditions<'tcx>, PrustiSymValue<'tcx>)>);

impl<'tcx> SymPureEncResult<'tcx> {
    pub fn from_sym_value(value: PrustiSymValue<'tcx>) -> Self {
        Self(vec![(PathConditions::new(), value)].into_iter().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = &(PrustiPathConditions<'tcx>, PrustiSymValue<'tcx>)> {
        self.0.iter()
    }

    pub fn subst(self, tcx: ty::TyCtxt<'tcx>, substs: &PrustiSubsts<'tcx>) -> Self {
        let mut result = BTreeSet::new();
        for (path_conditions, value) in self.0 {
            let path_conditions = path_conditions.subst(tcx, substs);
            let value = value.subst(tcx, substs);
            result.insert((path_conditions, value));
        }
        Self(result)
    }
}

pub struct PrustiSemantics;

pub type PrustiSymValSynthetic = ();
pub type PrustiPathConditions<'tcx> = PathConditions<'tcx, PrustiSymValSynthetic>;
pub type PrustiSymValue<'tcx> = SymValue<'tcx, PrustiSymValSynthetic>;
pub type PrustiSubsts<'tcx> = Substs<'tcx, PrustiSymValSynthetic>;

impl VerifierSemantics for PrustiSemantics {
    fn is_pure(&self, def_id: DefId) -> bool {
        crate::encoders::with_proc_spec(def_id, |proc_spec| {
            proc_spec.kind.is_pure().unwrap_or_default()
        })
        .unwrap_or_default()
    }

    type SymValSynthetic = PrustiSymValSynthetic;
}

impl SymPureEnc {
    pub fn encode<'tcx>(task: SymPureEncTask<'tcx>) -> SymPureEncResult<'tcx> {
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
                PrustiSemantics
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
