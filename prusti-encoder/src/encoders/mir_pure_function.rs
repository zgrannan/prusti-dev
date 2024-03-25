use prusti_rustc_interface::{
    middle::{mir, ty::{self, GenericArgs, Ty}},
    span::def_id::DefId,
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, ExprGen, FunctionIdent, Reify, UnknownArity};

use crate::{encoder_traits::function_enc::{FunctionEnc, MirFunctionEncOutput, MirFunctionEncOutputRef}, encoders::{
    domain::DomainEnc, lifted::{
        func_def_ty_params::LiftedTyParamsEnc,
        ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc}
    }, mir_pure::PureKind,
    most_generic_ty::extract_type_params,
    GenericEnc, LocalDef, MirLocalDefEnc, MirPureEnc, MirPureEncTask, MirSpecEnc
}};

pub struct MirFunctionEnc;

#[derive(Clone, Debug)]
pub enum MirFunctionEncError {
    Unsupported,
}


impl FunctionEnc for MirFunctionEnc {
    fn get_substs<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        GenericArgs::identity_for_item(vcx.tcx(), *def_id)
    }

    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "f_{}_CALLER", vcx.tcx().item_name(*def_id))
    }

    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId {
        *task_key
    }

    fn get_caller_def_id(task_key: &Self::TaskKey<'_>) -> Option<DefId> {
        None
    }
}

impl TaskEncoder for MirFunctionEnc {
    task_encoder::encoder_cache!(MirFunctionEnc);

    type TaskDescription<'vir> = (
        DefId, // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        DefId, // Caller DefID
    );

    type OutputRef<'vir> = MirFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncOutput<'vir>;
    type TaskKey<'tcx> = DefId;

    type EncodingError = MirFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.0
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
        Ok((<Self as FunctionEnc>::encode(*task_key, deps), ()))
    }
}
