use prusti_rustc_interface::middle::mir;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdent, UnknownArity, ViperIdent};

use crate::encoders::{
    lifted::func_def_ty_params::LiftedTyParamsEnc, MirLocalDefEnc, MirSpecEnc
};

use super::function_enc::FunctionEnc;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncError;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for ImpureFunctionEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

const ENCODE_REACH_BB: bool = false;

pub trait ImpureFunctionEnc
where
    Self: 'static
        + Sized
        + FunctionEnc
        + for<'vir> TaskEncoder<OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>>,
{
    /// Generates the identifier for the method; for a monomorphic encoding,
    /// this should be a name including (mangled) type arguments
    fn mk_method_ident<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        task_key: &Self::TaskKey<'vir>,
    ) -> ViperIdent<'vir>;

    fn encode<'vir>(
        _task_key: Self::TaskKey<'vir>,
        _deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<
        ImpureFunctionEncOutput<'vir>,
        EncodeFullError<'vir, Self>,
    > {
        unimplemented!()
    }
}
