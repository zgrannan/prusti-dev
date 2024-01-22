use prusti_rustc_interface::{
    middle::{ty::{self, TyKind}},
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies, TaskEncoderError};

use crate::util::{extract_type_params, MostGenericTy};

pub mod predicate;
pub mod domain;
pub mod snapshot;
pub mod viper_tuple;

pub fn require_local_for_ty<
    'tcx: 'vir,
    'vir,
    E: TaskEncoder<TaskDescription<'tcx> = MostGenericTy<'tcx>>>
(
    vcx: &'vir vir::VirCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir>,
) -> Result<E::OutputFullLocal<'vir>, TaskEncoderError<E>>
    where E: 'vir
{
    let (ty, args) = extract_type_params(vcx.tcx, ty);
    for arg in args {
        require_local_for_ty(vcx, arg, deps)?;
    }
    deps.require_local::<E>(ty)
}

pub fn require_ref_for_ty<
    'tcx: 'vir,
    'vir,
    E: TaskEncoder<TaskDescription<'tcx> = MostGenericTy<'tcx>>>
(
    vcx: &'vir vir::VirCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir>,
) -> Result<E::OutputRef<'vir>, TaskEncoderError<E>>
    where E: 'vir
{
    let (ty, args) = extract_type_params(vcx.tcx, ty);
    for arg in args {
        require_ref_for_ty(vcx, arg, deps)?;
    }
    deps.require_ref::<E>(ty)
}