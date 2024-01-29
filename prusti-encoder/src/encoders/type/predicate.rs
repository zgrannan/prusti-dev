use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{with_vcx, Type, TypeData};

use crate::{
    encoders::{GenericPredicateEnc, GenericPredicateEncOutputRef},
    util::extract_type_params,
};

use super::lifted::{LiftedTy, LiftedTyEnc};

pub struct PredicateEnc;

#[derive(Clone)]
pub struct PredicateEncOutputRef<'vir> {
    pub generic_predicate: GenericPredicateEncOutputRef<'vir>,
    pub ty: LiftedTy<'vir>,
}

impl<'vir> PredicateEncOutputRef<'vir> {

    pub fn method_assign_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        self_new_snap: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        assert!(self_ref.ty() == &TypeData::Ref);
        assert!(self_new_snap.ty() == self.snapshot());
        let mut args = vec![self_ref];
        args.extend(self.ty.arg_exprs(vcx));
        args.push(self_new_snap);
        vcx.alloc_slice(&args)
    }

    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        self_new_snap: vir::Expr<'vir>,
    ) -> vir::Stmt<'vir> {
        let args = self.method_assign_args(vcx, self_ref, self_new_snap);
        vcx.alloc(self.generic_predicate.method_assign.apply(vcx, args))
    }

    pub fn snapshot(
        &self
    ) -> Type<'vir> {
        self.generic_predicate.snapshot
    }

    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        args: &[vir::Expr<'vir>],
        perm: Option<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        vcx.mk_predicate_app_expr(
            self.generic_predicate.ref_to_pred.apply(
                vcx,
                args,
                perm
            )
        )
    }

    pub fn ref_to_pred_app<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        args: &[vir::Expr<'vir>],
        perm: Option<vir::Expr<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        self.generic_predicate.ref_to_pred.apply(
            vcx,
            args,
            perm
        )
    }

    pub fn ref_to_snap<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        args: &[vir::Expr<'vir>],
    ) -> vir::Expr<'vir> {
        self.generic_predicate.ref_to_snap.apply(vcx, args)
    }

    pub fn ref_to_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        self.generic_predicate
            .ref_to_args(vcx, self.ty, self_ref)
    }
}

impl<'vir> task_encoder::OutputRefAny for PredicateEncOutputRef<'vir> {}

impl TaskEncoder for PredicateEnc {
    task_encoder::encoder_cache!(PredicateEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = PredicateEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();

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
        with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx, *task_key);
            let generic_predicate = deps.require_ref::<GenericPredicateEnc>(generic_ty).unwrap();
            let ty = deps.require_ref::<LiftedTyEnc>(*task_key).unwrap();
            deps.emit_output_ref::<PredicateEnc>(
                *task_key,
                PredicateEncOutputRef {
                    generic_predicate,
                    ty
                },
            );
            for arg in args {
                deps.require_ref::<PredicateEnc>(arg).unwrap();
            }
            Ok(((), ()))
        })
    }

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputFullDependency<'vir> = ();

    type EnqueueingError = ();

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }
}
