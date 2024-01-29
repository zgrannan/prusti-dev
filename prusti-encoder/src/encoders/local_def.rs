use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdent, MethodIdent, PredicateIdent, TypeData, UnknownArity};

use crate::{
    encoders::{PredicateEnc, PredicateEncOutputRef},
    util::{extract_type_params, get_viper_type_value},
};

use super::{require_ref_for_ty, GenericEnc};

pub struct MirLocalDefEnc;
#[derive(Clone, Copy)]
pub struct MirLocalDefEncOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, LocalDef<'vir>>,
    pub arg_count: usize,
}
pub type MirLocalDefEncError = ();

pub struct EncodedTyParams<'vir>(&'vir [EncodedTyParam<'vir>]);

impl<'vir> EncodedTyParams<'vir> {
    pub fn new(ty_params: &'vir [EncodedTyParam<'vir>]) -> Self {
        EncodedTyParams(ty_params)
    }

    pub fn generics<'tcx>(&self) -> Vec<vir::LocalDecl<'vir>> {
        self.0
            .iter()
            .filter_map(|g| match g {
                EncodedTyParam::Generic(g) => Some(*g),
                EncodedTyParam::Instantiated(_) => None,
            })
            .collect::<Vec<_>>()
    }

    pub fn as_exprs<'tcx>(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::Expr<'vir>> {
        self.0.iter().map(|g| g.expr(vcx)).collect::<Vec<_>>()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum EncodedTyParam<'vir> {
    Generic(vir::LocalDecl<'vir>),
    Instantiated(vir::Expr<'vir>),
}

impl<'vir> From<vir::LocalDecl<'vir>> for EncodedTyParam<'vir> {
    fn from(decl: vir::LocalDecl<'vir>) -> Self {
        EncodedTyParam::Generic(decl)
    }
}

impl<'vir> From<vir::Expr<'vir>> for EncodedTyParam<'vir> {
    fn from(expr: vir::Expr<'vir>) -> Self {
        EncodedTyParam::Instantiated(expr)
    }
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

#[derive(Clone, Copy, Debug)]
pub struct TyOps<'vir> {
    pub ty_params: &'vir [EncodedTyParam<'vir>],
    pub ref_to_pred: PredicateIdent<'vir, UnknownArity<'vir>>,
    pub ref_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    pub snapshot: vir::Type<'vir>,
    pub method_assign: MethodIdent<'vir, UnknownArity<'vir>>,
}

impl<'vir> TyOps<'vir> {
    pub fn generics<'tcx>(&self) -> Vec<vir::LocalDecl<'vir>> {
        self.ty_params
            .iter()
            .filter_map(|g| match g {
                EncodedTyParam::Generic(g) => Some(*g),
                EncodedTyParam::Instantiated(_) => None,
            })
            .collect::<Vec<_>>()
    }

    fn ty_param_args<'tcx>(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::Expr<'vir>> {
        self.ty_params
            .iter()
            .map(|g| g.expr(vcx))
            .collect::<Vec<_>>()
    }

    pub fn ref_to_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        assert!(self_ref.ty() == &TypeData::Ref);
        let mut args = vec![self_ref];
        args.extend(self.ty_param_args(vcx));
        vcx.alloc_slice(&args)
    }

    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        self_new_snap: vir::Expr<'vir>,
    ) -> vir::Stmt<'vir> {
        let args = self.method_assign_args(vcx, self_ref, self_new_snap);
        vcx.alloc(self.method_assign.apply(vcx, args))
    }

    pub fn method_assign_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::Expr<'vir>,
        self_new_snap: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        assert!(self_ref.ty() == &TypeData::Ref);
        assert!(self_new_snap.ty() == self.snapshot);
        let mut args = vec![self_ref];
        args.extend(self.ty_param_args(vcx));
        args.push(self_new_snap);
        vcx.alloc_slice(&args)
    }
}

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::Local<'vir>,
    pub local_ex: vir::Expr<'vir>,
    pub impure_snap: vir::Expr<'vir>,
    pub impure_pred: vir::Expr<'vir>,
    pub ty: &'vir PredicateEncOutputRef<'vir>,
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'tcx> = (
        DefId,                    // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
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

        fn mk_local_def<'vir, 'tcx>(
            vcx: &'vir vir::VirCtxt<'tcx>,
            name: &'vir str,
            ty: &'vir PredicateEncOutputRef<'vir>,
            params: EncodedTyParams<'vir>,
        ) -> LocalDef<'vir> {
            let local = vcx.mk_local(name, &vir::TypeData::Ref);
            let local_ex = vcx.mk_local_ex_local(local);
            let args = ty.ref_to_args(vcx, params, local_ex);
            let impure_snap = ty.ref_to_snap.apply(vcx, args);
            let impure_pred = vcx.mk_predicate_app_expr(ty.ref_to_pred.apply(vcx, args, None));
            LocalDef {
                local,
                local_ex,
                impure_snap,
                impure_pred,
                ty,
            }
        }

        vir::with_vcx(|vcx| {
            let data = if let Some(local_def_id) = def_id.as_local() {
                let body =
                    vcx.body
                        .borrow_mut()
                        .get_impure_fn_body(local_def_id, substs, caller_def_id);
                let locals = IndexVec::from_fn_n(
                    |arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}p", arg.index());
                        let (ty, params) = get_predicate_ref_and_ty_substs(vcx, body.local_decls[arg].ty, deps);
                        mk_local_def(vcx, local, ty, params)
                    },
                    body.local_decls.len(),
                );
                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let param_env = vcx.tcx.param_env(caller_def_id.unwrap_or(def_id));
                let sig = vcx.tcx.subst_and_normalize_erasing_regions(
                    substs,
                    param_env,
                    vcx.tcx.fn_sig(def_id),
                );
                let sig = sig.skip_binder();

                let locals = IndexVec::from_fn_n(
                    |arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}p", arg.index());
                        let ty = if arg.index() == 0 {
                            sig.output()
                        } else {
                            sig.inputs()[arg.index() - 1]
                        };
                        let (ty, params) = get_predicate_ref_and_ty_substs(vcx, ty, deps);
                        mk_local_def(vcx, local, ty, params)
                    },
                    sig.inputs_and_output.len(),
                );

                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok((data, ()))
        })
    }
}

pub fn get_predicate_ref_and_ty_substs<'tcx: 'vir, 'vir>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir>,
) -> (&'vir PredicateEncOutputRef<'vir>, EncodedTyParams<'vir>) {
    let predicate_ref = require_ref_for_ty::<PredicateEnc>(vcx, ty, deps).unwrap();
    let ty_params = get_ty_params(vcx, ty, deps);
    (vcx.alloc(predicate_ref), ty_params)
}

pub fn get_ty_params<'tcx: 'vir, 'vir>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir>,
) -> EncodedTyParams<'vir> {
    let ty_params = if let ty::TyKind::Param(_) = ty.kind() {
        vec![get_viper_type_value(vcx, deps, ty)]
    } else {
        let (_, ty_params) = extract_type_params(vcx.tcx, ty);
        ty_params
            .into_iter()
            .map(|ty| get_viper_type_value(vcx, deps, ty))
            .collect::<Vec<_>>()
    };
    EncodedTyParams::new(vcx.alloc_slice(&ty_params))
}

pub fn get_ty_ops<'tcx: 'vir, 'vir>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir>,
) -> TyOps<'vir> {
    let predicate_ref = require_ref_for_ty::<PredicateEnc>(vcx, ty, deps).unwrap();
    let ty_params = if let ty::TyKind::Param(_) = ty.kind() {
        vec![get_viper_type_value(vcx, deps, ty)]
    } else {
        let (_, ty_params) = extract_type_params(vcx.tcx, ty);
        ty_params
            .into_iter()
            .map(|ty| get_viper_type_value(vcx, deps, ty))
            .collect::<Vec<_>>()
    };
    return TyOps {
        ty_params: vcx.alloc_slice(&ty_params),
        ref_to_pred: predicate_ref.ref_to_pred,
        ref_to_snap: predicate_ref.ref_to_snap,
        snapshot: predicate_ref.snapshot,
        method_assign: predicate_ref.method_assign,
    };
}
