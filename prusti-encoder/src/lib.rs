#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;

use prusti_interface::{environment::EnvBody, specs::typed::SpecificationItem};
use prusti_rustc_interface::{
    middle::ty,
    hir,
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> () {
    use task_encoder::TaskEncoder;

    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir().body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn |
            hir::def::DefKind::AssocFn => {
                vir::with_vcx(|vcx| {
                    let body = vcx.body.borrow_mut().get_impure_fn_body_identity(def_id);
                    mir_state_analysis::run_free_pcs(&body, vcx.tcx);
                });
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

}
