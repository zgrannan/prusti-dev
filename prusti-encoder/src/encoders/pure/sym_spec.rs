use middle::mir::{
    interpret::{ConstValue, Scalar},
    Constant,
};
use mir_state_analysis::symbolic_execution::value::SymValue;
use prusti_rustc_interface::{
    hir::lang_items,
    middle::{self, mir, ty},
    span::{def_id::DefId, DUMMY_SP},
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use crate::encoders::{mir_pure::PureKind, CapabilityEnc, MirPureEnc, SymPureEnc};
pub struct SymSpecEnc;

#[derive(Clone)]
pub struct SymSpecEncOutput<'vir> {
    pub pres: Vec<SymValue<'vir>>,
    pub posts: Vec<SymValue<'vir>>,
}
type SymSpecEncTask<'tcx> = (
    DefId,                    // The function annotated with specs
    ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    Option<DefId>,            // ID of the caller function, if any
);

impl SymSpecEnc {
    pub fn encode<'tcx, 'vir>(
        deps: &mut TaskEncoderDependencies<'vir>,
        task_key: SymSpecEncTask<'tcx>,
    ) -> SymSpecEncOutput<'tcx> {
        let (def_id, substs, caller_def_id) = task_key;

        eprintln!("def_id: {:?}", def_id);


        vir::with_vcx(|vcx| {
            let panic_lang_items = [
                vcx.tcx.lang_items().panic_fn().unwrap(),
                vcx.tcx.lang_items().begin_panic_fn().unwrap(),
            ];
            if panic_lang_items.contains(&def_id) {
                let false_constant = mir::Constant {
                    span: DUMMY_SP,
                    user_ty: None,
                    literal: mir::ConstantKind::from_bool(vcx.tcx, false),
                };
                return SymSpecEncOutput {
                    pres: vec![SymValue::Constant(false_constant.into())],
                    posts: vec![],
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
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: Some(def_id),
                    })
                })
                .collect::<Vec<_>>();

            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    SymPureEnc::encode(crate::encoders::SymPureEncTask {
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: Some(def_id),
                    })
                })
                .collect::<Vec<_>>();
            SymSpecEncOutput { pres, posts }
        })
    }
}
