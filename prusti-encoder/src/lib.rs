#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;

use prusti_interface::{environment::EnvBody, specs::typed::SpecificationItem};
use prusti_rustc_interface::{hir, middle::ty};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> () {
    use task_encoder::TaskEncoder;

    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    let mut item_names = vec![];
    let dir_path = "visualization/data";
    if std::path::Path::new(dir_path).exists() {
        std::fs::remove_dir_all(dir_path).expect("Failed to delete directory contents");
    }
    std::fs::create_dir_all(dir_path).expect("Failed to create directory for JSON file");

    for def_id in tcx.hir().body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                vir::with_vcx(|vcx| {
                    let body = vcx.body.borrow_mut().get_impure_fn_body_identity(def_id);
                    mir_state_analysis::run_free_pcs(&body, vcx.tcx, &dir_path);
                    item_names.push(format!("{}", tcx.item_name(body.body.source.def_id())));
                });
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    use std::{fs::File, io::Write};

    let file_path = format!("{}/functions.json", dir_path);


    let json_data =
        serde_json::to_string(&item_names).expect("Failed to serialize item names to JSON");
    let mut file = File::create(file_path).expect("Failed to create JSON file");
    file.write_all(json_data.as_bytes())
        .expect("Failed to write item names to JSON file");
}
