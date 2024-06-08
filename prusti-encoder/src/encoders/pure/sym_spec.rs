use middle::mir::interpret::{ConstValue, Scalar};
use mir_state_analysis::symbolic_execution::{
    path_conditions::PathConditions,
    value::{Constant, SymValue, Ty},
    ResultPath,
};
use prusti_rustc_interface::{
    hir::lang_items,
    middle::{self, mir::{self, PlaceElem}, ty},
    span::{def_id::DefId, DUMMY_SP},
};

use std::collections::BTreeSet;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use crate::encoders::{
    mir_pure::PureKind, sym_pure::{PrustiSymValue, SymPureEncResult}, CapabilityEnc, MirPureEnc, SymPureEnc,
};
pub struct SymSpecEnc;

#[derive(Clone)]
pub struct SymSpec<'tcx>(BTreeSet<SymPureEncResult<'tcx>>);

impl<'tcx> SymSpec<'tcx> {
    pub fn new() -> Self {
        Self(BTreeSet::new())
    }
    pub fn singleton(value: SymPureEncResult<'tcx>) -> Self {
        Self(vec![value].into_iter().collect())
    }

    pub fn into_iter(self) -> impl Iterator<Item = SymPureEncResult<'tcx>> {
        self.0.into_iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = &SymPureEncResult<'tcx>> {
        self.0.iter()
    }
}

#[derive(Clone)]
pub struct SymSpecEncOutput<'vir> {
    pub pres: SymSpec<'vir>,
    pub posts: SymSpec<'vir>,
}
type SymSpecEncTask<'tcx> = (
    DefId,                    // The function annotated with specs
    ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    Option<DefId>,            // ID of the caller function, if any
);

impl SymSpecEnc {
    pub fn spec_bool<'tcx>(tcx: ty::TyCtxt<'tcx>, b: bool) -> SymSpec<'tcx> {
        let constant = SymValue::Constant(Constant::from_bool(tcx, b));
        SymSpec::singleton(SymPureEncResult::from_sym_value(constant))
    }

    fn partial_eq_expr<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
        lhs: PrustiSymValue<'tcx>,
        rhs: PrustiSymValue<'tcx>,
    ) -> Option<PrustiSymValue<'tcx>> {
        match ty.kind() {
            ty::TyKind::Tuple(tys) => {
                let exprs = tys.iter().enumerate().map(|(i, ty)| {
                    let field = PlaceElem::Field(i.into(), ty);
                    let lhs_field = SymValue::Projection(field, Box::new(lhs.clone()));
                    let rhs_field = SymValue::Projection(field, Box::new(rhs.clone()));
                    Self::partial_eq_expr(tcx, ty, lhs_field, rhs_field)
                }).collect::<Option<Vec<_>>>()?;
                Some(SymValue::mk_conj(tcx, exprs))
            }
            ty::TyKind::Adt(adt_def, substs) => {
                if tcx.has_structural_eq_impls(ty) {
                    let lhs_discriminant = SymValue::Discriminant(Box::new(lhs));
                    let rhs_discriminant = SymValue::Discriminant(Box::new(rhs));
                    let discriminants_match = SymValue::BinaryOp(
                        tcx.types.bool,
                        mir::BinOp::Eq,
                        Box::new(lhs_discriminant),
                        Box::new(rhs_discriminant),
                    );
                    todo!()
                    // adt_def.variants.iter().map(|variant| {
                    // });
                } else {
                    None
                }
            }
            other => todo!("{:#?}", other),
        }
    }

    fn partial_eq_spec<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
        result: PrustiSymValue<'tcx>,
    ) -> SymSpecEncOutput<'tcx> {
        match ty.kind() {
            ty::TyKind::Tuple(tys) if tys.is_empty() => {
                return SymSpecEncOutput {
                    pres: SymSpec::new(),
                    posts: SymSpec::singleton(SymPureEncResult::from_sym_value(result)),
                };
            }
            ty::TyKind::Ref(_, ty, _) => {
                return Self::partial_eq_spec(tcx, *ty, result);
            }
            ty::TyKind::Adt(def_id, substs) => {
                todo!()
            }
            other => todo!("{:#?}", other),
        }
    }

    pub fn encode<'tcx, 'vir, T: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, T>,
        task_key: SymSpecEncTask<'tcx>,
    ) -> SymSpecEncOutput<'tcx> {
        let (def_id, substs, caller_def_id) = task_key;

        vir::with_vcx(|vcx| {
            let panic_lang_items = [
                vcx.tcx().lang_items().panic_fn().unwrap(),
                vcx.tcx().lang_items().begin_panic_fn().unwrap(),
            ];

            if panic_lang_items.contains(&def_id) {
                return SymSpecEncOutput {
                    pres: Self::spec_bool(vcx.tcx(), false),
                    posts: SymSpec::new(),
                };
            }

            if vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::eq" {
                let sig = vcx.tcx().subst_and_normalize_erasing_regions(
                    substs,
                    vcx.tcx().param_env(def_id),
                    vcx.tcx().fn_sig(def_id),
                );
                let input_ty = sig.input(0).skip_binder();
                return Self::partial_eq_spec(
                    vcx.tcx(),
                    input_ty,
                    SymValue::Var(2, vcx.tcx().types.bool)
                );
            }

            let specs = deps
                .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })
                .unwrap();

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    SymPureEnc::encode(crate::encoders::SymPureEncTask {
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx().param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: Some(def_id),
                    })
                })
                .collect::<BTreeSet<_>>();

            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let post = SymPureEnc::encode(crate::encoders::SymPureEncTask {
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx().param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: Some(def_id),
                    });
                    post
                })
                .collect::<BTreeSet<_>>();
            SymSpecEncOutput {
                pres: SymSpec(pres),
                posts: SymSpec(posts),
            }
        })
    }
}
