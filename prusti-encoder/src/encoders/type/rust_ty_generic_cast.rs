use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;
use vir::with_vcx;


use super::{generic_cast::{GenericCastEnc, GenericCastOutputRef}, most_generic_ty::extract_type_params};

/// Generates Viper functions to cast between generic and non-generic Viper
/// representations of a Rust value. See `GenericCastEnc` for more details.
pub struct RustTyGenericCastEnc;

#[derive(Clone)]
pub struct RustTyGenericCastEncOutputRef<'vir> {
    pub cast: GenericCastOutputRef<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for RustTyGenericCastEncOutputRef<'vir> {}

impl TaskEncoder for RustTyGenericCastEnc {
    task_encoder::encoder_cache!(RustTyGenericCastEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = RustTyGenericCastEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = ();

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

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
            let cast = deps.require_ref::<GenericCastEnc>(generic_ty).unwrap();
            deps.emit_output_ref::<RustTyGenericCastEnc>(
                *task_key,
                RustTyGenericCastEncOutputRef { cast },
            );
            for arg in args {
                deps.require_ref::<RustTyGenericCastEnc>(arg).unwrap();
            }
            Ok(((), ()))
        })
    }
}
