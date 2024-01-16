use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId
};

use rustc_middle::ty::Predicate;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdent, UnknownArity, PredicateIdent, MethodIdent, BinaryArity, TypeData};

use crate::encoders::{PredicateEncOutputRef, PredicateEnc};

use super::{GenericEnc, generic::{SNAPSHOT_PARAM_DOMAIN, TYP_DOMAIN}};

pub struct MirLocalDefEnc;
#[derive(Clone, Copy)]
pub struct MirLocalDefEncOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, LocalDef<'vir>>,
    pub arg_count: usize,
}
pub type MirLocalDefEncError = ();

#[derive(Clone, Copy, Debug)]
pub struct TyOps<'vir> {
    pub generics: &'vir [vir::LocalDecl<'vir>],
    pub ref_to_pred: PredicateIdent<'vir, UnknownArity<'vir>>,
    pub ref_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    pub snapshot: vir::Type<'vir>,
    pub method_assign: MethodIdent<'vir, BinaryArity<'vir>>,
}

impl <'vir> TyOps<'vir> {
    pub fn ref_to_args<'tcx>(&self, vcx: &'vir vir::VirCtxt<'tcx>, self_ref: vir::Expr<'vir>) -> &'vir [vir::Expr<'vir>] {
        assert!(self_ref.ty() == &TypeData::Ref);
        let mut args = vec![self_ref];
        for g in self.generics.iter() {
            args.push(vcx.mk_local_ex(g.name, g.ty));
        }
        vcx.alloc_slice(&args)
    }
}

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::Local<'vir>,
    pub local_ex: vir::Expr<'vir>,
    pub impure_snap: vir::Expr<'vir>,
    pub impure_pred: vir::Expr<'vir>,
    pub ty: &'vir TyOps<'vir>,
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'tcx> = (
        DefId, // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>, // ID of the caller function, if any
    );

    type OutputFullLocal<'vir> = MirLocalDefEncOutput<'vir>;

    type EncodingError = MirLocalDefEncError;

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
        let (def_id, substs, caller_def_id) = *task_key;
        deps.emit_output_ref::<Self>(*task_key, ());

        fn mk_local_def<'vir, 'tcx>(vcx: &'vir vir::VirCtxt<'tcx>, name: &'vir str, ty: TyOps<'vir>) -> LocalDef<'vir> {
            let local = vcx.mk_local(name, &vir::TypeData::Ref);
            let local_ex = vcx.mk_local_ex_local(local);
            let args = ty.ref_to_args(vcx, local_ex);
            let impure_snap = ty.ref_to_snap.apply(vcx, args);
            let impure_pred = vcx.mk_predicate_app_expr(ty.ref_to_pred.apply(vcx, args, None));
            LocalDef {
                local,
                local_ex,
                impure_snap,
                impure_pred,
                ty: vcx.alloc(ty),
            }
        }

        vir::with_vcx(|vcx| {
            let data = if let Some(local_def_id) = def_id.as_local() {
                let body = vcx.body.borrow_mut().get_impure_fn_body(local_def_id, substs, caller_def_id);
                let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                    let local = vir::vir_format!(vcx, "_{}p", arg.index());
                    let ty = get_ty_ops(vcx, body.local_decls[arg].ty, deps);
                    mk_local_def(vcx, local, ty)
                }, body.local_decls.len());
                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let param_env = vcx.tcx.param_env(caller_def_id.unwrap_or(def_id));
                let sig = vcx.tcx
                    .subst_and_normalize_erasing_regions(substs, param_env, vcx.tcx.fn_sig(def_id));
                let sig = sig.skip_binder();

                let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                    let local = vir::vir_format!(vcx, "_{}p", arg.index());
                    let ty = if arg.index() == 0 {
                        sig.output()
                    } else {
                        sig.inputs()[arg.index() - 1]
                    };
                    let ty = get_ty_ops(vcx, ty, deps);
                    mk_local_def(vcx, local, ty)
                }, sig.inputs_and_output.len());

                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok((data, ()))
        })
    }
}

pub fn get_ty_ops<'tcx: 'vir, 'vir>(vcx: &'vir vir::VirCtxt<'tcx>, ty: ty::Ty<'tcx>, deps: &mut TaskEncoderDependencies<'vir>) -> TyOps<'vir> {
    if let ty::TyKind::Param(p) = ty.kind() {
        let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
        return TyOps {
            generics: vcx.alloc_slice(&[vcx.mk_local_decl(p.name.as_str(), &TYP_DOMAIN)]),
            ref_to_pred: generic_ref.ref_to_pred.as_unknown_arity(),
            ref_to_snap: generic_ref.ref_to_snap.as_unknown_arity(),
            snapshot: &SNAPSHOT_PARAM_DOMAIN,
            method_assign: generic_ref.method_assign
        };
    } else {
        let predicate_ref = PredicateEnc::require_ref(ty, deps).unwrap();
        TyOps {
            generics: predicate_ref.generics,
            ref_to_pred: predicate_ref.ref_to_pred,
            ref_to_snap: predicate_ref.ref_to_snap,
            snapshot: predicate_ref.snapshot,
            method_assign: predicate_ref.method_assign,
        }

    }
}
