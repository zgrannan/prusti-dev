use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder};
use vir::{with_vcx, Expr, ExprGen, ExprGenData, VirCtxt};

use crate::encoders::SnapshotEnc;

use super::{
    lifted::{
        generic::LiftedGeneric,
        ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
    },
    most_generic_ty::extract_type_params,
    snapshot::{SnapshotEncOutput, SnapshotEncOutputRef},
};

pub struct RustTySnapshotsEnc;

#[derive(Clone)]
pub struct RustTySnapshotsEncOutputRef<'vir> {
    pub generic_snapshot: SnapshotEncOutputRef<'vir>,
}

#[derive(Clone)]
pub struct RustTySnapshotsEncOutput<'vir> {
    pub generic_snapshot: SnapshotEncOutput<'vir>,
    pub ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
}

impl<'vir> RustTySnapshotsEncOutput<'vir> {
    pub fn ty_arg_exprs<Curr, Next>(&self, vcx: &'vir VirCtxt<'_>) -> Vec<ExprGen<'vir, Curr, Next>> {
        self.ty_args.iter().map(|a| a.expr(vcx)).collect()
    }
}

impl<'vir> task_encoder::OutputRefAny for RustTySnapshotsEncOutputRef<'vir> {}

impl TaskEncoder for RustTySnapshotsEnc {
    task_encoder::encoder_cache!(RustTySnapshotsEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = RustTySnapshotsEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = RustTySnapshotsEncOutput<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let generic_snapshot = deps.require_ref::<SnapshotEnc>(generic_ty)?;
            deps.emit_output_ref(*task_key, RustTySnapshotsEncOutputRef { generic_snapshot })?;
            for arg in args.iter() {
                deps.require_ref::<RustTySnapshotsEnc>(*arg)?;
            }
            let generic_snapshot = deps.require_local::<SnapshotEnc>(generic_ty)?;
            let ty_args = vcx.alloc_slice(
                &args
                    .iter()
                    .map(|arg| {
                        deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*arg)
                            .unwrap()
                    })
                    .collect::<Vec<_>>(),
            );
            Ok((
                RustTySnapshotsEncOutput {
                    generic_snapshot,
                    ty_args,
                },
                (),
            ))
        })
    }
}
