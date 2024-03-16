use prusti_rustc_interface::{
    middle::ty::{GenericArgs, TyKind},
    span::def_id::DefId,
};
use task_encoder::TaskEncoder;

use super::generic::{LiftedGeneric, LiftedGenericEnc};

/// Encodes the generic arguments of a function definition.
pub struct LiftedFuncDefGenericsEnc;

impl TaskEncoder for LiftedFuncDefGenericsEnc {
    task_encoder::encoder_cache!(LiftedFuncDefGenericsEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputFullLocal<'vir> = &'vir [LiftedGeneric<'vir>];

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
            let ty_args = GenericArgs::identity_for_item(vcx.tcx, *task_key)
                .iter()
                .filter_map(|arg| {
                    let ty = arg.as_type()?;
                    if let TyKind::Param(p) = ty.kind() {
                        Some(deps.require_ref::<LiftedGenericEnc>(*p).unwrap())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            Ok((vcx.alloc_slice(&ty_args), ()))
        })
    }
}
