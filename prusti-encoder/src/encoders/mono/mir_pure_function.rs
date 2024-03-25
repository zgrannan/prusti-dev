use prusti_rustc_interface::{middle::ty::GenericArgs, span::def_id::DefId};
use std::fmt::Write;

use task_encoder::{TaskEncoder, TaskEncoderDependencies};

use crate::{
    encoder_traits::function_enc::{FunctionEnc, MirFunctionEncOutput, MirFunctionEncOutputRef},
    encoders::mir_pure_function::{MirFunctionEnc, MirFunctionEncError},
};

impl FunctionEnc for MirMonoFunctionEnc {
    fn get_substs<'tcx>(
        _vcx: &vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        task_key.1
    }

    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        let (def_id, substs, caller_def_id) = task_key;
        let mut extra = String::new();
        for s in substs.iter() {
            write!(extra, "_{s}").unwrap();
        }
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
