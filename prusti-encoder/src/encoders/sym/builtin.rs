use middle::{
    mir::interpret::{ConstValue, Scalar},
    ty::VariantDiscr,
};
use prusti_rustc_interface::{
    hir::lang_items,
    middle::{
        self,
        mir::{self, PlaceElem},
        ty::{self, VariantDef},
    },
    span::{def_id::DefId, DUMMY_SP},
};
use symbolic_execution::{context::SymExContext, value::Constant};

use crate::encoders::{
    sym_pure::{PrustiSymValSyntheticData, PrustiSymValue},
    sym_spec::mk_conj,
};

fn encode_discr<'sym, 'tcx>(
    arena: &'sym SymExContext<'tcx>,
    discr: VariantDiscr,
    ty: ty::Ty<'tcx>,
) -> PrustiSymValue<'sym, 'tcx> {
    match discr {
        VariantDiscr::Explicit(_) => todo!(),
        VariantDiscr::Relative(idx) => arena.mk_constant(Constant::from_u32(idx, ty)),
    }
}

pub fn partial_eq_expr<'sym, 'tcx>(
    arena: &'sym SymExContext<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    lhs: PrustiSymValue<'sym, 'tcx>,
    rhs: PrustiSymValue<'sym, 'tcx>,
) -> Option<PrustiSymValue<'sym, 'tcx>> {
    let ty = lhs.ty(tcx).rust_ty();
    match ty.kind() {
        ty::TyKind::Uint(..) | ty::TyKind::Int(..) => {
            Some(arena.mk_bin_op(tcx.types.bool, mir::BinOp::Eq, lhs, rhs))
        }
        ty::TyKind::Ref(..) => {
            let deref_lhs = arena.mk_projection(mir::ProjectionElem::Deref, lhs);
            let deref_rhs = arena.mk_projection(mir::ProjectionElem::Deref, rhs);
            partial_eq_expr(arena, tcx, deref_lhs, deref_rhs)
        }
        ty::TyKind::Tuple(tys) => {
            let exprs = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let field = PlaceElem::Field(i.into(), ty);
                    let lhs_field = arena.mk_projection(field, lhs);
                    let rhs_field = arena.mk_projection(field, rhs);
                    partial_eq_expr(arena, tcx, lhs_field, rhs_field)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(mk_conj(arena, tcx, exprs))
        }
        ty::TyKind::Adt(adt_def, substs) => {
            if tcx.has_structural_eq_impls(ty) {
                let lhs_discriminant = arena.mk_discriminant(lhs);
                let rhs_discriminant = arena.mk_discriminant(rhs);
                let mut iter = adt_def.variants().iter_enumerated();
                let (first_variant_idx, first_variant) = iter.next().unwrap();
                let first_case = encode_variant_eq(
                    arena,
                    tcx,
                    first_variant,
                    substs,
                    arena.mk_projection(
                        PlaceElem::Downcast(Some(first_variant.name), first_variant_idx),
                        lhs,
                    ),
                    arena.mk_projection(
                        PlaceElem::Downcast(Some(first_variant.name), first_variant_idx),
                        rhs,
                    ),
                )?;
                if adt_def.variants().len() == 1 {
                    return Some(first_case);
                }
                let discriminants_match = arena.mk_bin_op(
                    tcx.types.bool,
                    mir::BinOp::Eq,
                    lhs_discriminant,
                    rhs_discriminant,
                );
                let deep_eq = iter.try_fold(first_case, |acc, (variant_idx, variant)| {
                    Some(
                        arena.mk_synthetic(arena.alloc(PrustiSymValSyntheticData::If(
                            arena.mk_bin_op(
                                tcx.types.bool,
                                mir::BinOp::Eq,
                                lhs_discriminant,
                                encode_discr(
                                    arena,
                                    variant.discr,
                                    lhs_discriminant.ty(tcx).rust_ty(),
                                ),
                            ),
                            encode_variant_eq(
                                arena,
                                tcx,
                                variant,
                                substs,
                                arena.mk_projection(
                                    PlaceElem::Downcast(Some(variant.name), variant_idx),
                                    lhs,
                                ),
                                arena.mk_projection(
                                    PlaceElem::Downcast(Some(variant.name), variant_idx),
                                    rhs,
                                ),
                            )?,
                            acc,
                        ))),
                    )
                })?;
                Some(arena.mk_synthetic(
                    arena.alloc(PrustiSymValSyntheticData::And(discriminants_match, deep_eq)),
                ))
            } else {
                None
            }
        }
        ty::TyKind::Uint(..) => Some(arena.mk_bin_op(tcx.types.bool, mir::BinOp::Eq, lhs, rhs)),
        ty::TyKind::Param(..) => None, // TODO
        other => todo!("partial_eq_expr: {:?}", other),
    }
}

fn encode_variant_eq<'sym, 'tcx>(
    arena: &'sym SymExContext<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    variant: &VariantDef,
    substs: ty::GenericArgsRef<'tcx>,
    lhs: PrustiSymValue<'sym, 'tcx>,
    rhs: PrustiSymValue<'sym, 'tcx>,
) -> Option<PrustiSymValue<'sym, 'tcx>> {
    Some(mk_conj(
        arena,
        tcx,
        variant
            .fields
            .iter_enumerated()
            .map(|(i, field)| {
                let field_ty = field.ty(tcx, substs);
                let field = PlaceElem::Field(i.into(), field_ty);
                let lhs_field = arena.mk_projection(field, lhs);
                let rhs_field = arena.mk_projection(field, rhs);
                partial_eq_expr(arena, tcx, lhs_field, rhs_field)
            })
            .collect::<Option<Vec<_>>>()?,
    ))
}
