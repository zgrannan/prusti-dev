use prusti_rustc_interface::{middle::{mir, ty::GenericArgs}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{Reify, FunctionIdent, UnknownArity, CallableIdent};

use crate::encoders::{
    lifted_func_def_generics::LiftedFuncDefGenericsEnc, mir_pure::PureKind, MirLocalDefEnc, MirPureEnc, MirPureEncTask, MirSpecEnc
};

pub struct MirFunctionEnc;

#[derive(Clone, Debug)]
pub enum MirFunctionEncError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirFunctionEncOutputRef<'vir> {
    pub function_ref: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirFunctionEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirFunctionEncOutput<'vir> {
    pub function: vir::Function<'vir>,
}

impl TaskEncoder for MirFunctionEnc {
    task_encoder::encoder_cache!(MirFunctionEnc);

    type TaskDescription<'vir> = (
        DefId, // ID of the function
        DefId, // Caller DefID
    );

    type OutputRef<'vir> = MirFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncOutput<'vir>;

    type EncodingError = MirFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        let (def_id, caller_def_id) = *task_key;
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec|
            def_spec.trusted.extract_inherit().unwrap_or_default()
        ).unwrap_or_default();

        vir::with_vcx(|vcx| {
            let substs = GenericArgs::identity_for_item(vcx.tcx, def_id);
            let local_defs = deps.require_local::<MirLocalDefEnc>(
                (def_id, substs, Some(caller_def_id)),
            ).unwrap();

            tracing::debug!("encoding {def_id:?}");

            let (krate, index) = (caller_def_id.krate, caller_def_id.index.index());
            let function_name = vir::vir_format!(vcx, "f_{}_CALLER_{krate}_{index}", vcx.tcx.item_name(def_id));
            let ty_arg_decls = deps.require_local::<LiftedFuncDefGenericsEnc>(def_id).unwrap();
            let mut ident_args = ty_arg_decls.iter().map(|arg| arg.ty()).collect::<Vec<_>>();
            ident_args.extend((1..=local_defs.arg_count)
                .map(mir::Local::from)
                .map(|def_idx| local_defs.locals[def_idx].ty.snapshot)
            );
            let ident_args = UnknownArity::new(vcx.alloc_slice(&ident_args));
            let return_type = local_defs.locals[mir::RETURN_PLACE].ty;
            let function_ref = FunctionIdent::new(function_name, ident_args, return_type.snapshot);
            deps.emit_output_ref::<Self>(*task_key, MirFunctionEncOutputRef { function_ref });

            let spec = deps.require_local::<MirSpecEnc>(
                (def_id, substs, Some(caller_def_id), true)
            ).unwrap();

            let mut func_args = ty_arg_decls.iter().map(|arg| arg.decl()).collect::<Vec<_>>();
            func_args.extend((1..=local_defs.arg_count).map(mir::Local::from).map(|arg| vcx.alloc(vir::LocalDeclData {
                name: local_defs.locals[arg].local.name,
                ty: local_defs.locals[arg].ty.snapshot,
            })));

            let expr = if trusted {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_local::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx.param_env(def_id),
                        substs,
                        caller_def_id,
                    })
                    .unwrap()
                    .expr;

                Some(expr.reify(vcx, (def_id, spec.pre_args)))
            };

            tracing::debug!("finished {def_id:?}");

            Ok((
                MirFunctionEncOutput {
                    function: vcx.mk_function(
                        function_name,
                        vcx.alloc_slice(&func_args),
                        local_defs.locals[mir::RETURN_PLACE].ty.snapshot,
                        vcx.alloc_slice(&spec.pres),
                        vcx.alloc_slice(&spec.posts),
                        expr
                    ),
                },
                (),
            ))
        })
    }
}
