use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{CallableIdent, DomainParamData, FunctionIdent, NullaryArityAny, UnknownArity};

use crate::encoders::{most_generic_ty::extract_type_params, GenericEnc};

use super::most_generic_ty::MostGenericTy;

#[derive(Clone)]
pub struct LiftedTyFunctionEncOutputRef<'vir> {
    /// Takes as input the generics for this type (if any),
    /// and returns the resulting type
    pub function: vir::FunctionIdent<'vir, UnknownArity<'vir>>,
}

impl<'vir> OutputRefAny for LiftedTyFunctionEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct LiftedTyFunctionEncOutput<'vir> {
    pub domain: vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>,
    pub function: vir::DomainFunction<'vir>,
}

pub struct LiftedTyFunctionEnc;

impl TaskEncoder for LiftedTyFunctionEnc {
    task_encoder::encoder_cache!(LiftedTyFunctionEnc);
    type TaskDescription<'tcx> = MostGenericTy<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputRef<'vir> = LiftedTyFunctionEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = LiftedTyFunctionEncOutput<'vir>;

    type OutputFullDependency<'vir> = ();

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir>,
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
        let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
        vir::with_vcx(|vcx| {
            let (ty_constructor, args) = extract_type_params(vcx.tcx, task_key.ty());
            let type_function_args = vcx.alloc_slice(&vec![generic_ref.type_snapshot; args.len()]);
            let type_function_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "s_{}_type", ty_constructor.get_vir_base_name(vcx)),
                UnknownArity::new(&type_function_args),
                generic_ref.type_snapshot,
            );
            deps.emit_output_ref::<Self>(*task_key, LiftedTyFunctionEncOutputRef {
                function: type_function_ident,
            });
            let type_function = vcx.mk_domain_function(
                false,
                type_function_ident.name(),
                &type_function_args,
                generic_ref.type_snapshot,
            );
            let result = LiftedTyFunctionEncOutput {
                domain: task_key.get_vir_domain_ident(vcx),
                function: type_function,
            };
            Ok((result, ()))
        })
    }
}
