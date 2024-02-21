use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;
use vir::with_vcx;

use crate::{encoders::SnapshotEnc, util::extract_type_params};

use super::{generic_cast::{GenericCastEnc, GenericCastOutput, GenericCastOutputRef}, snapshot::{SnapshotEncOutput, SnapshotEncOutputRef}};

pub struct RustTyGenericCastEnc;

#[derive(Clone)]
pub struct RustTyGenericCastEncOutputRef<'vir> {
    pub cast: GenericCastOutputRef<'vir>,
}

#[derive(Clone)]
pub struct RustTyGenericCastEncOutput<'vir> {
    pub cast: GenericCastOutput<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for RustTyGenericCastEncOutputRef<'vir> {}

impl TaskEncoder for RustTyGenericCastEnc {
    task_encoder::encoder_cache!(RustTyGenericCastEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = RustTyGenericCastEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = RustTyGenericCastEncOutput<'vir>;

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
            assert!(!matches!(task_key.kind(), ty::TyKind::Param(_)));
            let (generic_ty, args) = extract_type_params(vcx.tcx, *task_key);
            let cast = deps.require_ref::<GenericCastEnc>(generic_ty).unwrap();
            deps.emit_output_ref::<RustTyGenericCastEnc>(
                *task_key,
                RustTyGenericCastEncOutputRef { cast },
            );
            for arg in args {
                if !matches!(arg.kind(), ty::TyKind::Param(_)) {
                    deps.require_ref::<RustTyGenericCastEnc>(arg).unwrap();
                }
            }
            let cast = deps
                .require_local::<GenericCastEnc>(generic_ty)
                .unwrap();
            Ok((RustTyGenericCastEncOutput { cast }, ()))
        })
    }
}
