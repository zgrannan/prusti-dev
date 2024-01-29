use prusti_rustc_interface::middle::ty::{self, TyKind};
use task_encoder::{OutputRefAny, TaskEncoder};
use vir::with_vcx;

use crate::{encoders::GenericEnc, util::extract_type_params};

use super::domain::DomainEnc;

#[derive(Clone, Copy, Debug)]
pub enum EncodedTyParam<'vir> {
    Generic(vir::LocalDecl<'vir>),
    Instantiated(vir::Expr<'vir>),
}

impl<'vir, 'tcx> EncodedTyParam<'vir> {
    pub fn from_param(
        vcx: &'vir vir::VirCtxt<'tcx>,
        param: &'tcx ty::ParamTy,
        generic_ty: vir::Type<'vir>,
    ) -> Self {
        EncodedTyParam::Generic(vcx.mk_local_decl(param.name.as_str(), generic_ty))
    }

    pub fn expr(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> vir::Expr<'vir> {
        match self {
            EncodedTyParam::Generic(g) => vcx.mk_local_ex(g.name, g.ty),
            EncodedTyParam::Instantiated(e) => e,
        }
    }

    pub fn decl(&self) -> Option<vir::LocalDecl<'vir>> {
        match self {
            EncodedTyParam::Generic(g) => Some(g),
            EncodedTyParam::Instantiated(_) => None,
        }
    }
}

impl<'vir> OutputRefAny for EncodedTyParam<'vir> {}

pub struct TyParamEnc;

impl TaskEncoder for TyParamEnc {
    task_encoder::encoder_cache!(TyParamEnc);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputRef<'vir> = EncodedTyParam<'vir>;

    type OutputFullLocal<'vir> = ();

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
            let output_ref =
            if let TyKind::Param(p) = task_key.kind() {
                    EncodedTyParam::from_param(
                        vcx,
                        p,
                        deps.require_ref::<GenericEnc>(()).unwrap().type_snapshot,
                    )
            } else {
                let (generic_ty, args) = extract_type_params(vcx.tcx, *task_key);
                let type_function = deps
                    .require_ref::<DomainEnc>(generic_ty)
                    .unwrap()
                    .type_function;
                let args = args
                    .into_iter()
                    .map(|ty| deps.require_ref::<Self>(ty).unwrap().expr(vcx))
                    .collect::<Vec<_>>();
                    EncodedTyParam::Instantiated(type_function.apply(vcx, &args))
            };
            deps.emit_output_ref::<TyParamEnc>(*task_key, output_ref);
        });
        Ok(((), ()))
    }
}
