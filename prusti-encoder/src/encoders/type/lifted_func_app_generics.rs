use prusti_rustc_interface::middle::ty::GenericArgsRef;
use task_encoder::TaskEncoder;

use super::lifted::{LiftedTy, LiftedTyEnc};
pub struct LiftedFuncAppGenericsEnc;

impl TaskEncoder for LiftedFuncAppGenericsEnc {
    task_encoder::encoder_cache!(LiftedFuncAppGenericsEnc);
    type TaskDescription<'tcx> = GenericArgsRef<'tcx>;

    type OutputFullLocal<'vir> = &'vir [LiftedTy<'vir>];

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
        deps.emit_output_ref::<Self>(*task_key, ());
        vir::with_vcx(|vcx| {
            let ty_args = task_key
                .iter()
                .filter_map(|arg| {
                    let ty = arg.as_type()?;
                    Some(deps.require_local::<LiftedTyEnc>(ty).unwrap())
                })
                .collect::<Vec<_>>();
            Ok((vcx.alloc_slice(&ty_args), ()))
        })
    }
}
