use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;
use vir::with_vcx;

use crate::{encoders::GenericSnapshotEnc, util::extract_type_params};

use super::generic_snapshot::{GenericSnapshotEncOutput, GenericSnapshotEncOutputRef};

pub struct SnapshotEnc;

#[derive(Clone)]
pub struct SnapshotEncOutputRef<'vir> {
    pub generic_snapshot: GenericSnapshotEncOutputRef<'vir>,
}

#[derive(Clone)]
pub struct SnapshotEncOutput<'vir> {
    pub generic_snapshot: GenericSnapshotEncOutput<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for SnapshotEncOutputRef<'vir> {}

impl TaskEncoder for SnapshotEnc {
    task_encoder::encoder_cache!(SnapshotEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = SnapshotEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = SnapshotEncOutput<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputFullDependency<'vir> = ();

    type EnqueueingError = ();

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
        with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx, *task_key);
            let generic_snapshot = deps.require_ref::<GenericSnapshotEnc>(generic_ty).unwrap();
            deps.emit_output_ref::<SnapshotEnc>(
                *task_key,
                SnapshotEncOutputRef { generic_snapshot },
            );
            for arg in args {
                deps.require_ref::<SnapshotEnc>(arg).unwrap();
            }
            let generic_snapshot = deps
                .require_local::<GenericSnapshotEnc>(generic_ty)
                .unwrap();
            Ok((SnapshotEncOutput { generic_snapshot }, ()))
        })
    }
}
