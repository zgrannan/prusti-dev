use mir_state_analysis::symbolic_execution::value::SymValue;
use prusti_rustc_interface::{
    ast,
    ast::Local,
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
    type_ir::sty::TyKind,
};
use std::collections::HashMap;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
// TODO: replace uses of `CapabilityEnc` with `SnapshotEnc`
use crate::encoders::{
    CapabilityEnc, ConstEnc, MirBuiltinEnc, MirFunctionEnc, SnapshotEnc, ViperTupleEnc,
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
pub struct SymPureEncOutput<'vir> {
    pub expr: SymValue<'vir>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymPureEncTask<'tcx> {
    pub kind: PureKind,
    pub parent_def_id: DefId,             // ID of the function
    pub param_env: ty::ParamEnv<'tcx>,    // param environment at the usage site
    pub substs: ty::GenericArgsRef<'tcx>, // type substitutions at the usage site
    pub caller_def_id: Option<DefId>,     // Caller/Use DefID
}

impl SymPureEnc {
    pub fn encode<'tcx>(task: SymPureEncTask<'tcx>) -> SymValue<'tcx> {
        let kind = task.kind;
        let def_id = task.parent_def_id;
        let substs = task.substs;
        let caller_def_id = task.caller_def_id;
        vir::with_vcx(move |vcx| {
            let body = match kind {
                PureKind::Closure => {
                    vcx.body_mut()
                        .get_closure_body(def_id, substs, caller_def_id.unwrap())
                }
                PureKind::Spec => {
                    vcx.body_mut()
                        .get_spec_body(def_id, substs, caller_def_id.unwrap())
                }
                PureKind::Pure => vcx
                    .body_mut()
                    .get_pure_fn_body(def_id, substs, caller_def_id),
                PureKind::Constant(promoted) => todo!(),
            };
            let body = &body.body();
            let mut fpcs_analysis = mir_state_analysis::run_free_pcs(body, vcx.tcx());
            fpcs_analysis.analysis_for_bb(mir::START_BLOCK);
            let symbolic_execution = mir_state_analysis::run_symbolic_execution(
                body,
                vcx.tcx(),
                mir_state_analysis::run_free_pcs(body, vcx.tcx()),
            );
            symbolic_execution.paths.into_iter().next().unwrap().2 // TODO
        })
    }
}
