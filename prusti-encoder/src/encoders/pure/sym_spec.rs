use middle::mir::{
    interpret::{ConstValue, Scalar},
    Constant,
};
use mir_state_analysis::symbolic_execution::{
    path_conditions::PathConditions, value::SymValue, ResultPath,
};
use prusti_rustc_interface::{
    hir::lang_items,
    middle::{self, mir, ty},
    span::{def_id::DefId, DUMMY_SP},
};

use std::collections::BTreeSet;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use crate::encoders::{
    mir_pure::PureKind, sym_pure::SymPureEncResult, CapabilityEnc, MirPureEnc, SymPureEnc,
};
pub struct SymSpecEnc;

type SymSpec<'tcx> = BTreeSet<SymPureEncResult<'tcx>>;

#[derive(Clone)]
pub struct SymSpecEncOutput<'vir> {
    pub pres: SymSpec<'vir>,
    pub posts: SymSpec<'vir>,
}
type SymSpecEncTask<'tcx> = (
    DefId,                    // The function annotated with specs
    ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    Option<DefId>,            // ID of the caller function, if any
);

impl SymSpecEnc {
    pub fn encode<'tcx, 'vir, T: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, T>,
        task_key: SymSpecEncTask<'tcx>,
    ) -> SymSpecEncOutput<'tcx> {
        let (def_id, substs, caller_def_id) = task_key;

        vir::with_vcx(|vcx| {
            let panic_lang_items = [
                vcx.tcx().lang_items().panic_fn().unwrap(),
                vcx.tcx().lang_items().begin_panic_fn().unwrap(),
            ];
            if panic_lang_items.contains(&def_id) {
                let false_constant = mir::Constant {
                    span: DUMMY_SP,
                    user_ty: None,
                    literal: mir::ConstantKind::from_bool(vcx.tcx(), false),
                };
                return SymSpecEncOutput {
                    pres: vec![SymPureEncResult::from_sym_value(SymValue::Constant(
                        false_constant.into(),
                    ))]
                    .into_iter()
                    .collect(),
                    posts: BTreeSet::new(),
                };
            }
            let specs = deps
                .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })
                .unwrap();

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    SymPureEnc::encode(crate::encoders::SymPureEncTask {
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx().param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: Some(def_id),
                    })
                })
                .collect::<BTreeSet<_>>();

            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let post = SymPureEnc::encode(crate::encoders::SymPureEncTask {
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx().param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: Some(def_id),
                    });
                    eprintln!("post: {:#?}", post);
                    post
                })
                .collect::<BTreeSet<_>>();
            SymSpecEncOutput { pres, posts }
        })
    }
}
