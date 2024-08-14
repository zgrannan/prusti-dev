#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(never_type)]
#![feature(let_chains)]
#![allow(unused_imports)]
#![feature(return_position_impl_trait_in_trait)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod debug;
mod encoders;
mod encoder_traits;
mod sctx;
pub mod request;

use std::{
    collections::BTreeSet,
    hash::{Hash, Hasher},
};

use prusti_interface::environment::EnvBody;
use prusti_rustc_interface::{hir, middle::ty};
use symbolic_execution::context::SymExContext;
use task_encoder::TaskEncoder;

use crate::encoders::{
    lifted::{
        casters::{CastTypeImpure, CastTypePure, CastersEnc},
        ty_constructor::TyConstructorEnc,
    },
    predicate::PredicateEnc,
    MirPolyImpureEnc, SymFunctionEnc,
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> request::RequestWithContext {
    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));
    sctx::init_scx(SymExContext::new(tcx));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir().body_owners() {
        eprintln!("Start encoding method {:?}", def_id);
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                    let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                    let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();
                    (is_pure, is_trusted)
                })
                .unwrap_or_default();

                if !is_trusted {
                    let substs = ty::GenericArgs::identity_for_item(tcx, def_id);
                    eprintln!("Start encoding method impure {:?}", def_id);
                    let res = crate::encoders::SymImpureEnc::encode(
                        (def_id.as_local().unwrap(), substs, None),
                        false,
                    );
                    if let Err(err) = res {
                        panic!("error encoding impure function: {err:?}");
                    }
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
        eprintln!("Done encoding method {:?}", def_id);
    }

    eprintln!("encoded methods!");

    let mut function_names = BTreeSet::default();

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
    for output in crate::encoders::sym_spec::SymSpecEnc::all_outputs() {
        function_names.extend(output.debug_ids());
    }
    for output in crate::encoders::SymImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
        viper_code.push_str(&format!("{:?}\n", output.backwards_fns_domain));
        program_methods.push(output.method);
        if let Some(backwards_method) = output.backwards_method {
            program_methods.push(backwards_method);
            viper_code.push_str(&format!("{:?}\n", backwards_method));
        }
        function_names.extend(output.debug_ids);
        program_domains.push(output.backwards_fns_domain);
    }

    header(&mut viper_code, "functions");
    for output in crate::encoders::PureFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "sym functions");
    for output in SymFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
        function_names.extend(output.debug_ids);
    }

    header(&mut viper_code, "MIR builtins");
    for output in crate::encoders::MirBuiltinEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "generics");
    for output in crate::encoders::GenericEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.type_snapshot));
        viper_code.push_str(&format!("{:?}\n", output.param_snapshot));
        program_domains.push(output.type_snapshot);
        program_domains.push(output.param_snapshot);
    }

    header(&mut viper_code, "pure generic casts");
    for cast_functions in CastersEnc::<CastTypePure>::all_outputs() {
        for cast_function in cast_functions {
            viper_code.push_str(&format!("{:?}\n", cast_function));
            program_functions.push(cast_function);
        }
    }

    header(&mut viper_code, "impure generic casts");
    for cast_methods in CastersEnc::<CastTypeImpure>::all_outputs() {
        for cast_method in cast_methods {
            viper_code.push_str(&format!("{:?}\n", cast_method));
            program_methods.push(cast_method);
        }
    }

    header(&mut viper_code, "snapshots");
    for output in crate::encoders::DomainEnc_all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output));
        program_domains.push(output);
    }

    header(&mut viper_code, "type constructors");
    for output in TyConstructorEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.domain));
        program_domains.push(output.domain);
    }

    header(&mut viper_code, "types");
    for output in PredicateEnc::all_outputs() {
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

    let program = vir::with_vcx(|vcx| {
        vcx.mk_program(
            vcx.alloc_slice(&program_fields),
            vcx.alloc_slice(&program_domains),
            vcx.alloc_slice(&program_predicates),
            vcx.alloc_slice(&program_functions),
            vcx.alloc_slice(&program_methods),
        )
    });

    /*
    let source_path = std::path::Path::new("source/path"); // TODO: env.name.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    */

    if let Ok(dir) = std::env::var("PCS_VIS_DATA_DIR") {
        let function_map: std::collections::HashMap<String, String> = function_names
            .into_iter()
            .map(|name| {
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                name.hash(&mut hasher);
                let hash = format!("{:x}", hasher.finish());
                (hash, name)
            })
            .collect();
        let json_content = serde_json::to_string(&function_map).unwrap();
        let file_path = std::path::Path::new(&dir).join("functions.json");
        std::fs::write(file_path, json_content).unwrap();
    }
    request::RequestWithContext {
        program: program.to_ref(),
    }
}
