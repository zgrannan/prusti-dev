use crate::encoders::rust_ty_generic_cast::RustTyGenericCastEnc;
use prusti_rustc_interface::middle::ty;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::VirCtxt;

use super::{
    generic::GenericEncOutputRef, generic_cast::GenericCastOutputRef,
    rust_ty_generic_cast::RustTyGenericCastEncOutputRef,
};

#[derive(Copy, Hash, PartialEq, Eq, Clone, Debug)]
pub struct CastArgs<'tcx> {
    pub expected: ty::Ty<'tcx>,
    pub actual: ty::Ty<'tcx>,
}

#[derive(Clone)]
pub enum PureGenericCastOutputRef<'vir> {
    NoCast,
    Cast(vir::FunctionIdent<'vir, vir::UnaryArity<'vir>>),
}

impl<'vir> PureGenericCastOutputRef<'vir> {
    pub fn apply<Curr, Next>(
        &self,
        vcx: &'vir VirCtxt<'_>,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            PureGenericCastOutputRef::NoCast => expr,
            PureGenericCastOutputRef::Cast(f) => f.apply(vcx, [expr]),
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for PureGenericCastOutputRef<'vir> {}

pub struct PureGenericCastEnc;

impl TaskEncoder for PureGenericCastEnc {
    task_encoder::encoder_cache!(PureGenericCastEnc);
    type TaskDescription<'tcx> = CastArgs<'tcx>;
    type OutputRef<'vir> = PureGenericCastOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();
    type EncodingError = ();

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
        let expected_is_param = matches!(task_key.expected.kind(), ty::Param(_));
        let actual_is_param = matches!(task_key.actual.kind(), ty::Param(_));
        let output_ref = if expected_is_param == actual_is_param {
            PureGenericCastOutputRef::NoCast
        } else {
            if actual_is_param {
                // expected is concrete type, `actual`  should be concretized
                if let GenericCastOutputRef::CastFunctions { make_concrete, .. } = deps
                    .require_ref::<RustTyGenericCastEnc>(task_key.expected)
                    .unwrap()
                    .cast
                {
                    PureGenericCastOutputRef::Cast(make_concrete)
                } else {
                    unreachable!()
                }
            } else {
                // expected is generic type, `actual` should be be made generic
                if let GenericCastOutputRef::CastFunctions { make_generic, .. } = deps
                    .require_ref::<RustTyGenericCastEnc>(task_key.actual)
                    .unwrap()
                    .cast
                {
                    PureGenericCastOutputRef::Cast(make_generic)
                } else {
                    unreachable!()
                }
            }
        };
        deps.emit_output_ref::<Self>(*task_key, output_ref);
        Ok(((), ()))
    }
}
