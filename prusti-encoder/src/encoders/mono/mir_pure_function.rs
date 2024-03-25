use prusti_rustc_interface::{
    span::def_id::DefId,
    middle::{mir, ty::GenericArgs}
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, FunctionIdent, Reify, UnknownArity};

use crate::{
    encoder_traits::function_enc::{FunctionEnc, MirFunctionEncOutput, MirFunctionEncOutputRef},
    encoders::{
        domain::DomainEnc,
        lifted::{
            func_def_ty_params::LiftedTyParamsEnc,
            ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
        },
        mir_pure::PureKind,
        mir_pure_function::{
            MirFunctionEnc, MirFunctionEncError,
        },
        most_generic_ty::extract_type_params,
        GenericEnc, MirLocalDefEnc, MirPureEnc, MirPureEncTask, MirSpecEnc,
    },
};

impl FunctionEnc for MirMonoFunctionEnc {
    fn get_substs<'vir, 'tcx>(
        _vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        task_key.1
    }

    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        let (def_id, substs, caller_def_id)  = task_key;
        let extra: String = substs.iter().map(|s| format!("_{s}")).collect();
        let (krate, index) = (caller_def_id.krate, caller_def_id.index.index());
        vir::vir_format_identifier!(
            vcx,
            "f_{}{extra}_CALLER_{krate}_{index}",
            vcx.tcx().item_name(*def_id)
        )
    }

    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId {
        task_key.0
    }

    fn get_caller_def_id(task_key: &Self::TaskKey<'_>) -> Option<DefId> {
        Some(task_key.2)
    }
}

pub struct MirMonoFunctionEnc;

impl TaskEncoder for MirMonoFunctionEnc {
    task_encoder::encoder_cache!(MirMonoFunctionEnc);

    type TaskDescription<'vir> = <MirFunctionEnc as TaskEncoder>::TaskDescription<'vir>;

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
        Ok((<Self as FunctionEnc>::encode(*task_key, deps), ()))
    }
}
