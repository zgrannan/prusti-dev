use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{with_vcx, Type, TypeData};

use crate::encoders::{PredicateEnc, PredicateEncOutputRef};

use super::{lifted::{LiftedTy, LiftedTyEnc}, most_generic_ty::extract_type_params};

pub struct RustTyPredicatesEnc;

#[derive(Clone)]
pub struct RustTyPredicatesEncOutputRef<'vir> {
    /// The predicate output for the "most generic version" of the input type
    pub generic_predicate: PredicateEncOutputRef<'vir>,

    /// The lifted representation of the input type, as a Viper value
    pub ty: LiftedTy<'vir>,
}

impl<'vir> RustTyPredicatesEncOutputRef<'vir> {
    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        self_new_snap: vir::Expr<'vir>,
    ) -> vir::Stmt<'vir> {
        assert!(self_ref.ty() == &TypeData::Ref);
        assert_eq!(
            self_new_snap.ty(),
            self.snapshot(),
            "type mismatch, self_new_snap created at {}",
            self_new_snap.debug_info
        );
        let mut args = vec![self_ref];
        args.extend(self.ty.arg_exprs(vcx));
        args.push(self_new_snap);
        vcx.alloc(self.generic_predicate.method_assign.apply(vcx, &args))
    }

    pub fn snapshot(&self) -> Type<'vir> {
        self.generic_predicate.snapshot
    }

    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        args: &[vir::Expr<'vir>],
        perm: Option<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        vcx.mk_predicate_app_expr(self.generic_predicate.ref_to_pred.apply(vcx, args, perm))
    }

    pub fn ref_to_pred_app<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        args: &[vir::Expr<'vir>],
        perm: Option<vir::Expr<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        self.generic_predicate.ref_to_pred.apply(vcx, args, perm)
    }

    pub fn ref_to_snap<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        args: &[vir::Expr<'vir>],
    ) -> vir::Expr<'vir> {
        self.generic_predicate.ref_to_snap.apply(vcx, args)
    }

    /// Arguments to `ref_to_pred` and `ref_to_snap`.
    pub fn ref_to_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        self.generic_predicate.ref_to_args(vcx, self.ty, self_ref)
    }
}

impl<'vir> task_encoder::OutputRefAny for RustTyPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for RustTyPredicatesEnc {
    task_encoder::encoder_cache!(RustTyPredicatesEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = RustTyPredicatesEncOutputRef<'vir>;
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
            let generic_predicate = deps.require_ref::<PredicateEnc>(generic_ty).unwrap();
            let ty = deps.require_local::<LiftedTyEnc>(*task_key).unwrap();
            deps.emit_output_ref::<RustTyPredicatesEnc>(
                *task_key,
                RustTyPredicatesEncOutputRef {
                    generic_predicate,
                    ty,
                },
            );
            for arg in args {
                deps.require_ref::<RustTyPredicatesEnc>(arg).unwrap();
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
