#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;
pub mod request;

use prusti_interface::{environment::EnvBody, specs::typed::SpecificationItem};
use prusti_rustc_interface::{
    middle::ty,
    hir,
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> request::RequestWithContext {
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
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                        let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                        let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();
                        (is_pure, is_trusted)
                }).unwrap_or_default();

                if !(is_trusted && is_pure) {
                    let substs = ty::GenericArgs::identity_for_item(tcx, def_id);
                    let res = crate::encoders::SymImpureEnc::encode((def_id, substs, None));
                    assert!(res.is_ok());
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    fn header(code: &mut String, title: &str) {
        code.push_str("// -----------------------------\n");
        code.push_str(&format!("// {}\n", title));
        code.push_str("// -----------------------------\n");
    }
    let mut viper_code = String::new();

    let mut program_fields = vec![];
    let mut program_domains = vec![];
    let mut program_predicates = vec![];
    let mut program_functions = vec![];
    let mut program_methods = vec![];

    header(&mut viper_code, "methods");
    for (_, output) in crate::encoders::MirLocalFieldEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.field));
    }
    for (_, output) in crate::encoders::SymImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
        program_methods.push(output.method);
    }

    header(&mut viper_code, "functions");
    for (_, output) in crate::encoders::MirFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "MIR builtins");
    for (_, output) in crate::encoders::MirBuiltinEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "generics");
    for (_, output) in crate::encoders::GenericEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.snapshot_param));
        program_domains.push(output.snapshot_param);
        viper_code.push_str(&format!("{:?}\n", output.predicate_param));
        program_predicates.push(output.predicate_param);
        viper_code.push_str(&format!("{:?}\n", output.domain_type));
        program_domains.push(output.domain_type);
    }

    header(&mut viper_code, "snapshots");
    for (_, output) in crate::encoders::DomainEnc_all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output));
        program_domains.push(output);
    }

    header(&mut viper_code, "types");
    for (ty, output) in crate::encoders::PredicateEnc_all_outputs() {
        header(&mut viper_code, &format!("{ty}"));
        for field in output.fields {
            viper_code.push_str(&format!("{:?}", field));
            program_fields.push(field);
        }
        for field_projection in output.ref_to_field_refs {
            viper_code.push_str(&format!("{:?}", field_projection));
            program_functions.push(field_projection);
        }
        viper_code.push_str(&format!("{:?}\n", output.unreachable_to_snap));
        program_functions.push(output.unreachable_to_snap);
        viper_code.push_str(&format!("{:?}\n", output.function_snap));
        program_functions.push(output.function_snap);
        for pred in output.predicates {
            viper_code.push_str(&format!("{:?}\n", pred));
            program_predicates.push(pred);
        }
        viper_code.push_str(&format!("{:?}\n", output.method_assign));
        program_methods.push(output.method_assign);
    }

    std::fs::write("local-testing/simple.vpr", viper_code).unwrap();

    let program = vir::with_vcx(|vcx| vcx.mk_program(
        vcx.alloc_slice(&program_fields),
        vcx.alloc_slice(&program_domains),
        vcx.alloc_slice(&program_predicates),
        vcx.alloc_slice(&program_functions),
        vcx.alloc_slice(&program_methods),
    ));

    /*
    let source_path = std::path::Path::new("source/path"); // TODO: env.name.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    */

    request::RequestWithContext {
        program: program.to_ref(),
    }
}
