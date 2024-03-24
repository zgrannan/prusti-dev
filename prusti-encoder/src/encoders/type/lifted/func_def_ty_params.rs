use prusti_rustc_interface::middle::ty::{self, ParamTy, Ty, TyKind};
use std::collections::HashSet;
use task_encoder::TaskEncoder;

use super::generic::{LiftedGeneric, LiftedGenericEnc};

pub struct LiftedTyParamsEnc;

impl TaskEncoder for LiftedTyParamsEnc {
    task_encoder::encoder_cache!(LiftedTyParamsEnc);
    type TaskDescription<'tcx> = ty::GenericArgsRef<'tcx>;

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
            let ty_args = task_key
                .iter()
                .filter_map(|arg| arg.as_type())
                .flat_map(extract_ty_params);
            let ty_args = unique(ty_args)
                .map(|ty| deps.require_ref::<LiftedGenericEnc>(ty).unwrap())
                .collect::<Vec<_>>();
            Ok((vcx.alloc_slice(&ty_args), ()))
        })
    }
}

fn unique<'tcx>(iter: impl IntoIterator<Item = ParamTy>) -> impl Iterator<Item = ParamTy> {
    let mut seen = HashSet::new();
    iter.into_iter().filter(move |item| seen.insert(*item))
}

fn extract_ty_params(ty: Ty<'_>) -> Vec<ParamTy> {
    match ty.kind() {
        TyKind::Param(p) => vec![*p],
        TyKind::Adt(_, args) => args
            .iter()
            .filter_map(|arg| arg.as_type())
            .flat_map(|arg| extract_ty_params(arg))
            .collect(),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => vec![],
        other => todo!("{:?}", other),
    }
}
