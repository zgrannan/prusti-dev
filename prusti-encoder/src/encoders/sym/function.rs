use cfg_if::cfg_if;
use prusti_rustc_interface::{middle::ty::GenericArgs, span::def_id::DefId};
use task_encoder::{encoder_cache, OutputRefAny, TaskEncoder};
use vir::{
    vir_format, vir_format_identifier, CallableIdent, Function, FunctionIdent, UnknownArity,
};

use crate::encoders::{
    lifted::func_def_ty_params::LiftedTyParamsEnc, rust_ty_snapshots::RustTySnapshotsEnc,
    FunctionCallTaskDescription,
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

    type OutputFullLocal<'vir> = Function<'vir>;

    type OutputFullDependency<'vir> = ()
        where Self: 'vir;

    type EnqueueingError = ();

    type EncodingError = ();

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
                    )
                    let substs = task_key.substs;
                    let def_id = task_key.def_id;
                } else {
                    let def_id = *task_key;
                    let substs = GenericArgs::identity_for_item(vcx.tcx(), def_id);
                    let function_ident = vir_format_identifier!(
                        vcx,
                        "pure_{}",
                        vcx.tcx().def_path_str(task_key)
                    );
                }
            }
            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut ident_args = ty_arg_decls.iter().map(|arg| arg.ty()).collect::<Vec<_>>();
            let sig = vcx.tcx().fn_sig(def_id).skip_binder();
            let inputs = sig.inputs().skip_binder();
            ident_args.extend(inputs.iter().map(|input| {
                deps.require_ref::<RustTySnapshotsEnc>(*input)
                    .unwrap()
                    .generic_snapshot
                    .snapshot
            }));
            let output = sig.output().skip_binder();
            let return_type = deps
                .require_ref::<RustTySnapshotsEnc>(output)
                .unwrap()
                .generic_snapshot
                .snapshot;
            let ident_decls = ident_args
                .iter()
                .enumerate()
                .map(|(idx, arg)| vcx.mk_local_decl(vir_format!(vcx, "arg_{}", idx), arg));
            let function_ident = FunctionIdent::new(
                function_ident,
                UnknownArity::new(vcx.alloc_slice(&ident_args)),
                return_type,
            );
            deps.emit_output_ref(*task_key, SymFunctionEncOutputRef { function_ident })?;
            let function = vcx.mk_function(
                function_ident.name().to_str(),
                vcx.alloc_slice(&ident_decls.collect::<Vec<_>>()),
                return_type,
                &[],
                &[],
                None,
            );
            Ok((function, ()))
        })
    }
}
