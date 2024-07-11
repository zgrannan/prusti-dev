use std::collections::hash_map::DefaultHasher;

use cfg_if::cfg_if;
use prusti_rustc_interface::{
    middle::{
        mir,
        ty::{self, GenericArgs},
    },
    span::def_id::DefId,
};
use std::hash::{Hash, Hasher};
use symbolic_execution::context::SymExContext;
use task_encoder::{encoder_cache, OutputRefAny, TaskEncoder};
use vir::{
    vir_format, vir_format_identifier, CallableIdent, Function, FunctionIdent, UnknownArity,
};

use crate::{
    encoder_traits::pure_function_enc::{mk_type_assertion, PureFunctionEnc},
    encoders::{
        lifted::func_def_ty_params::LiftedTyParamsEnc,
        rust_ty_snapshots::RustTySnapshotsEnc,
        sym::{builtin::partial_eq_expr, expr::SymExprEncoder},
        sym_pure::{PrustiSubsts, PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult},
        sym_spec::SymSpecEnc,
        FunctionCallTaskDescription, PureKind, SymPureEnc, SymPureEncTask,
    },
};

pub struct SymFunctionEnc;

impl<'vir> OutputRefAny for SymFunctionEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct SymFunctionEncOutputRef<'vir> {
    pub function_ident: FunctionIdent<'vir, UnknownArity<'vir>>,
}

impl TaskEncoder for SymFunctionEnc {
    encoder_cache!(SymFunctionEnc);
    type TaskDescription<'vir> = FunctionCallTaskDescription<'vir>;

    #[cfg(feature = "mono_function_encoding")]
    type TaskKey<'vir> = Self::TaskDescription<'vir>;

    #[cfg(not(feature = "mono_function_encoding"))]
    type TaskKey<'vir> = DefId;

    type OutputRef<'vir> = SymFunctionEncOutputRef<'vir>
        where Self: 'vir;

    type OutputFullLocal<'vir> = (Function<'vir>, String);

    type OutputFullDependency<'vir> = ()
        where Self: 'vir;

    type EnqueueingError = ();

    type EncodingError = String;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        #[cfg(feature = "mono_function_encoding")]
        return *task;

        #[cfg(not(feature = "mono_function_encoding"))]
        return task.def_id;
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            cfg_if! {
                if #[cfg(feature="mono_function_encoding")] {
                    let extra: String = task_key.substs.iter().map(|s| format!("_{s}")).collect();
                    let function_ident = vir_format_identifier!(
                        vcx,
                        "pure_{}_{}_{:?}",
                        vcx.tcx().def_path_str(task_key.def_id),
                        extra,
                        task_key.caller_def_id
                    );
                    let substs = task_key.substs;
                    let def_id = task_key.def_id;
                    let caller_def_id = Some(task_key.caller_def_id);
                } else {
                    let def_id = *task_key;
                    let substs = GenericArgs::identity_for_item(vcx.tcx(), def_id);
                    let function_ident = vir_format_identifier!(
                        vcx,
                        "pure_{}",
                        vcx.tcx().def_path_str(task_key)
                    );
                    let caller_def_id = None;
                }
            }
            eprintln!("IDENT: {:?}", function_ident);
            eprintln!("Substs: {:?}", substs);
            eprintln!("Def ID: {:?}", def_id);
            eprintln!("Caller Def ID: {:?}", caller_def_id);
            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut ident_args = ty_arg_decls.iter().map(|arg| arg.ty()).collect::<Vec<_>>();
            let sig = vcx.tcx().subst_and_normalize_erasing_regions(
                substs,
                vcx.tcx().param_env(def_id),
                vcx.tcx().fn_sig(def_id),
            );
            let inputs = sig.inputs().skip_binder();
            let input_tys = inputs
                .iter()
                .map(|input| {
                    deps.require_ref::<RustTySnapshotsEnc>(*input)
                        .unwrap()
                        .generic_snapshot
                        .snapshot
                })
                .collect::<Vec<_>>();
            ident_args.extend(input_tys.iter());
            let output = sig.output().skip_binder();
            let return_type = deps
                .require_ref::<RustTySnapshotsEnc>(output)
                .unwrap()
                .generic_snapshot
                .snapshot;
            let decls = ty_arg_decls
                .iter()
                .map(|t| t.decl())
                .chain(
                    input_tys
                        .iter()
                        .enumerate()
                        .map(|(idx, arg)| vcx.mk_local_decl(vir_format!(vcx, "arg_{}", idx), arg)),
                )
                .collect::<Vec<_>>();
            let function_ident = FunctionIdent::new(
                function_ident,
                UnknownArity::new(vcx.alloc_slice(&ident_args)),
                return_type,
            );
            deps.emit_output_ref(*task_key, SymFunctionEncOutputRef { function_ident })?;
            let arena = SymExContext::new(vcx.tcx());
            let spec = SymSpecEnc::encode(&arena, deps, (def_id, substs, None));
            let symvars: Vec<_> = decls
                .iter()
                .skip(ty_arg_decls.len())
                .map(|d| vcx.mk_local_ex(d.name, d.ty))
                .collect();
            let type_preconditions = inputs
                .iter()
                .zip(symvars.iter())
                .filter_map(|(ty, vir_arg)| mk_type_assertion(vcx, deps, vir_arg, *ty))
                .collect::<Vec<_>>();
            let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
                def_spec.trusted.extract_inherit().unwrap_or_default()
            })
            .unwrap_or_default();
            let debug_fn_name = vcx.tcx().def_path_str_with_args(def_id, substs);
            let debug_output_dir = std::env::var("PCS_VIS_DATA_DIR").map(|dir| {
                let mut hasher = DefaultHasher::new();
                debug_fn_name.hash(&mut hasher);
                let hash = format!("{:x}", hasher.finish());
                format!("{}/{}", dir, hash)
            });
            let body = if !trusted && def_id.is_local() {
                Some(SymPureEnc::encode(
                    &arena,
                    SymPureEncTask {
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx().param_env(def_id),
                        substs,
                        caller_def_id,
                    },
                    debug_output_dir.ok().as_deref(),
                ))
            } else if vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::eq"
                || vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::ne"
            {
                let expr = partial_eq_expr(
                    &arena,
                    vcx.tcx(),
                    arena.mk_var(0, inputs[0]),
                    arena.mk_var(1, inputs[1]),
                );
                expr.map(|expr| {
                    let expr = if vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::ne" {
                        arena.mk_unary_op(vcx.tcx().types.bool, mir::UnOp::Not, expr)
                    } else {
                        expr
                    };
                    SymPureEncResult::from_sym_value(expr)
                })
            } else {
                None
            };
            let mut encoder = SymExprEncoder::new(vcx, &arena, symvars, def_id);

            // The postcondition of the function may refer to the result, the symvar after the
            // symvars for the function arguments is this result
            let postcondition_substs = PrustiSubsts::singleton(
                inputs.len(),
                arena.mk_synthetic(arena.alloc(PrustiSymValSyntheticData::Result(output))),
            );

            let body = if let Some(body) = body {
                Some(encoder.encode_pure_body(deps, &body).unwrap())
            } else {
                None
            };

            let function = vcx.mk_function(
                function_ident.name().to_str(),
                vcx.alloc_slice(&decls),
                return_type,
                vcx.alloc_slice(
                    &type_preconditions
                        .into_iter()
                        .chain(
                            spec.pres
                                .into_iter()
                                .map(|s| encoder.encode_pure_spec(deps, s, None).unwrap()),
                        )
                        .collect::<Vec<_>>(),
                ),
                vcx.alloc_slice(
                    &spec
                        .posts
                        .into_iter()
                        .map(|s| {
                            encoder
                                .encode_pure_spec(deps, s, Some(&postcondition_substs))
                                .unwrap()
                        })
                        .collect::<Vec<_>>(),
                ),
                body,
            );
            Ok(((function, debug_fn_name), ()))
        })
    }
}
