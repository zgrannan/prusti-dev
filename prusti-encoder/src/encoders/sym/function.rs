use std::collections::{hash_map::DefaultHasher, BTreeSet};

use cfg_if::cfg_if;
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir,
        ty::{self, GenericArgs},
    },
    span::def_id::DefId,
};
use std::{
    collections::BTreeMap,
    hash::{Hash, Hasher},
};
use symbolic_execution::{context::SymExContext, value::SymVar};
use task_encoder::{encoder_cache, OutputRefAny, TaskEncoder};
use vir::{
    vir_format, vir_format_identifier, CallableIdent, FullIdent, Function, FunctionIdent,
    Identifiable, ShortIdent, UnknownArity, ViperIdent,
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

#[derive(Clone)]
pub struct SymFunctionEncOutput<'vir> {
    pub function: Function<'vir>,
    pub debug_ids: BTreeSet<String>,
}

struct PureFunctionIdent<'vir>(FunctionCallTaskDescription<'vir>);

#[cfg(feature = "mono_function_encoding")]
impl<'vir> Identifiable for PureFunctionIdent<'vir> {
    fn to_full_ident(&self) -> FullIdent {
        vir::with_vcx(|vcx| {
            let extra: String = self.0.substs.iter().map(|s| format!("_{s}")).collect();
            format!(
                "pure_{}_{}_{:?}",
                vcx.tcx().def_path_str(self.0.def_id),
                extra,
                self.0.caller_def_id
            )
        })
    }

    fn preferred_idents(&self) -> Vec<String> {
        vir::with_vcx(|vcx| {
            let base_name = vcx.tcx().item_name(self.0.def_id).to_string();
            let extra: String = self.0.substs.iter().map(|s| format!("_{s}")).collect();
            vec![
                format!("pure_{}", base_name),
                format!("pure_{}_{}", base_name, extra),
                ViperIdent::sanitize_with_underscores(&self.to_full_ident()),
            ]
        })
    }
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

    type OutputFullLocal<'vir> = SymFunctionEncOutput<'vir>;

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
        let function_ident = vir::with_vcx(|vcx| {
            cfg_if! {
                if #[cfg(feature="mono_function_encoding")] {
                    vcx.get_ident(PureFunctionIdent(*task_key))
                } else {
                    vir_format_identifier!(
                        vcx,
                        "pure_{}",
                        vcx.tcx().def_path_str(task_key)
                    )
                }
            }
        });
        vir::with_vcx(|vcx| {
            cfg_if! {
                if #[cfg(feature="mono_function_encoding")] {
                    let substs = task_key.substs;
                    let def_id = task_key.def_id;
                    let caller_def_id = Some(task_key.caller_def_id);
                } else {
                    let def_id = *task_key;
                    let substs = GenericArgs::identity_for_item(vcx.tcx(), def_id);
                    let caller_def_id = None;
                }
            }
            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut ident_args = ty_arg_decls.iter().map(|arg| arg.ty()).collect::<Vec<_>>();
            let sig = vcx.tcx().instantiate_and_normalize_erasing_regions(
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
            let spec = deps
                .require_local::<SymSpecEnc>((def_id, substs, None))
                .unwrap();
            let mut debug_ids = spec.debug_ids();
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
                    debug_output_dir.ok(),
                ))
            } else if vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::eq"
                || vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::ne"
            {
                let expr = partial_eq_expr(
                    &arena,
                    vcx.tcx(),
                    arena.mk_var(SymVar::Normal(0), inputs[0]),
                    arena.mk_var(SymVar::Normal(1), inputs[1]),
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
            let encoder = SymExprEncoder::new(
                vcx,
                &arena,
                (0..inputs.len())
                    .map(|i| {
                        (
                            mir::Local::from_usize(i + 1),
                            arena.mk_var(SymVar::Normal(i), inputs[i]),
                        )
                    })
                    .collect(),
                symvars,
                def_id,
            );

            // The postcondition of the function may refer to the result, the symvar after the
            // symvars for the function arguments is this result
            let postcondition_substs = PrustiSubsts::singleton(
                inputs.len(),
                arena.mk_synthetic(arena.alloc(PrustiSymValSyntheticData::Result(output))),
            );

            let body = if let Some(body) = body {
                Some(
                    encoder
                        .encode_pure_body(deps, &body)
                        .map(|body| body.to_expr(vcx))
                        .map_err(|e| task_encoder::EncodeFullError::EncodingError(e, None))?,
                )
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
                                .flat_map(|s| encoder.encode_pure_spec(deps, s).unwrap().clauses),
                        )
                        .collect::<Vec<_>>(),
                ),
                vcx.alloc_slice(
                    &spec
                        .posts
                        .into_iter()
                        .flat_map(|s| {
                            encoder
                                .encode_pure_spec(deps, s.subst(&arena, &postcondition_substs))
                                .unwrap()
                                .clauses
                        })
                        .collect::<Vec<_>>(),
                ),
                body,
            );
            debug_ids.insert(debug_fn_name);
            Ok((
                SymFunctionEncOutput {
                    function,
                    debug_ids,
                },
                (),
            ))
        })
    }
}
