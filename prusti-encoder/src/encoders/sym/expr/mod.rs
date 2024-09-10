use prusti_rustc_interface::{
    abi,
    index::IndexVec,
    middle::{
        mir::{self, interpret::Scalar, ProjectionElem},
        ty::{self, GenericArgs, TyKind},
    },
    span::def_id::{DefId, LocalDefId},
    target::abi::{VariantIdx, FIRST_VARIANT},
};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditionPredicateAtom},
    transform::SymValueTransformer,
    value::{AggregateKind, BackwardsFn, Substs, SymValueKind, SymVar},
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{
    domain,
    lifted::{
        aggregate_cast::{AggregateSnapArgsCastEnc, AggregateSnapArgsCastEncTask, AggregateType},
        cast::{CastArgs, CastToEnc},
        casters::CastTypePure,
        func_app_ty_params::LiftedFuncAppTyParamsEnc,
        rust_ty_cast::RustTyCastersEnc,
    },
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym_pure::{
        PrustiPathConditions, PrustiSubsts, PrustiSymValSynthetic, PrustiSymValSyntheticData,
        PrustiSymValue, SymPureEncResult,
    },
    sym_spec::SymSpecEnc,
    ConstEnc, FunctionCallTaskDescription, MirBuiltinEnc, MirBuiltinEncTask, SymFunctionEnc,
};
use std::collections::BTreeMap;

use super::assertion::AssertionEncoder;

mod r#ref;
mod fn_call;
mod old;

type EncodePCResult<'vir, T> = Result<EncodedPC<'vir>, T>;
type EncodePureSpecResult<'vir, T> = Result<EncodedPureSpec<'vir>, T>;
pub type EncodePCAtomResult<'vir, T> = Result<EncodedPCAtom<'vir>, T>;
pub type EncodeSymValueResult<'vir, T> = Result<vir::Expr<'vir>, T>;
type PrustiPathConditionAtom<'sym, 'tcx> =
    PathConditionAtom<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

pub struct EncodedPureSpec<'vir> {
    pub clauses: Vec<vir::Expr<'vir>>,
}

impl<'vir> EncodedPureSpec<'vir> {
    pub fn to_expr(&self, vcx: &'vir vir::VirCtxt<'_>) -> vir::Expr<'vir> {
        vcx.mk_conj(vcx.alloc_slice(&self.clauses))
    }

    pub fn exhale_stmts(&self, vcx: &'vir vir::VirCtxt<'_>) -> Vec<vir::Stmt<'vir>> {
        self.clauses
            .iter()
            .map(|c| vcx.mk_exhale_stmt(*c))
            .collect::<Vec<_>>()
    }
}

pub struct SymExprEncoder<'vir: 'tcx, 'sym, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    pub arena: &'sym SymExContext<'tcx>,
    old_values: BTreeMap<mir::Local, PrustiSymValue<'sym, 'tcx>>,
    substs: BTreeMap<SymVar, vir::Expr<'vir>>,
    def_id: DefId,
}

impl<'vir, 'sym, 'tcx> SymExprEncoder<'vir, 'sym, 'tcx> {
    pub fn with_old_values(
        &self,
        old_values: BTreeMap<mir::Local, PrustiSymValue<'sym, 'tcx>>,
    ) -> Self {
        Self {
            old_values,
            arena: self.arena,
            vcx: self.vcx,
            substs: self.substs.clone(),
            def_id: self.def_id,
        }
    }
    pub fn new(
        vcx: &'vir vir::VirCtxt<'tcx>,
        arena: &'sym SymExContext<'tcx>,
        old_values: BTreeMap<mir::Local, PrustiSymValue<'sym, 'tcx>>,
        substs: BTreeMap<SymVar, vir::Expr<'vir>>,
        def_id: DefId,
    ) -> Self {
        Self {
            vcx,
            arena,
            old_values,
            substs,
            def_id,
        }
    }

    pub fn encode_sym_value<'slf, 'enc, T: TaskEncoder<EncodingError = String>>(
        &'slf self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        sym_value: PrustiSymValue<'sym, 'tcx>,
        in_old: bool,
    ) -> EncodeSymValueResult<'vir, String>
    where
        T: 'vir,
    {
        // let sym_value = sym_value.optimize(self.arena, self.vcx.tcx());
        match &sym_value.kind {
            SymValueKind::Var(var, ..) => {
                if in_old {
                    if let SymVar::Input(i) = var {
                        return self.encode_sym_value(
                            deps,
                            self.old_values.get(i).cloned().unwrap(),
                            false,
                        );
                    }
                }
                self.substs
                    .get(var)
                    .cloned()
                    .ok_or_else(|| format!("No symvar {:?}.", var))
            }
            SymValueKind::Constant(c) => Ok(deps
                .require_local::<ConstEnc>((c.literal(), 0, self.def_id))
                .unwrap()),
            SymValueKind::BinaryOp(res_ty, op, lhs, rhs) => {
                let l_ty = lhs.ty(self.vcx.tcx()).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx()).rust_ty();
                let lhs = self.encode_sym_value(deps, lhs, in_old)?;
                let rhs = self.encode_sym_value(deps, rhs, in_old)?;
                let viper_fn = deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::BinOp(
                        *res_ty, *op, l_ty, r_ty,
                    ))
                    .unwrap()
                    .function;
                Ok(viper_fn.apply(self.vcx, &[lhs, rhs]))
            }
            SymValueKind::UnaryOp(ty, op, expr) => {
                let expr = self.encode_sym_value(deps, expr, in_old)?;
                let viper_fn = deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::UnOp(*ty, *op, *ty))
                    .unwrap()
                    .function;
                Ok(viper_fn.apply(self.vcx, &[expr]))
            }
            SymValueKind::Aggregate(kind, exprs) => {
                if let AggregateKind::PCS(ty, _) = kind
                    && ty.is_ref()
                {
                    let mutability = match ty.kind() {
                        TyKind::Ref(_, _, mutability) => *mutability,
                        _ => unreachable!("AggregateKind::PCS with non-reference type: {:?}", ty),
                    };
                    return self.encode_ref(deps, exprs[0], mutability);
                }
                let vir_exprs = exprs
                    .iter()
                    .map(|e| self.encode_sym_value(deps, e, in_old))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = deps
                    .require_local::<RustTySnapshotsEnc>(kind.ty().rust_ty())
                    .unwrap();
                let sl = match kind.variant_idx() {
                    Some(idx) if kind.is_enum(self.vcx.tcx()) => {
                        ty.generic_snapshot
                            .specifics
                            .expect_enumlike()
                            .unwrap()
                            .variants[idx.as_usize()]
                        .fields
                    }
                    None if kind.is_enum(self.vcx.tcx()) => {
                        // We don't have any encoding of an unknown enum variant, so return it's concrete downcast
                        return Ok(vir_exprs[0]);
                    }
                    _ => ty.generic_snapshot.specifics.get_structlike().unwrap(),
                };
                let field_tys = exprs
                    .iter()
                    .map(|e| e.ty(self.vcx.tcx()).rust_ty())
                    .collect::<Vec<_>>();
                let ty_caster = deps
                    .require_local::<AggregateSnapArgsCastEnc>(AggregateSnapArgsCastEncTask {
                        tys: field_tys,
                        aggregate_type: match kind {
                            AggregateKind::Rust(
                                mir::AggregateKind::Adt(def_id, variant_idx, ..),
                                _,
                            ) => AggregateType::Adt {
                                def_id: *def_id,
                                variant_index: *variant_idx,
                            },
                            AggregateKind::Rust(mir::AggregateKind::Tuple, _) => {
                                AggregateType::Tuple
                            }
                            AggregateKind::Rust(mir::AggregateKind::Closure(..), _) => {
                                AggregateType::Closure
                            }
                            AggregateKind::PCS(ty, variant_idx) => match ty.kind() {
                                ty::TyKind::Adt(def, _) => AggregateType::Adt {
                                    def_id: def.did(),
                                    variant_index: variant_idx.unwrap_or(FIRST_VARIANT),
                                },
                                ty::TyKind::Tuple(..) => AggregateType::Tuple,
                                ty::TyKind::Closure(..) => AggregateType::Closure,
                                _ => todo!("{:?}", ty.kind()),
                            },
                            other => todo!("aggregate kind {:?}", other),
                        },
                    })
                    .unwrap();
                let casted_args = ty_caster.apply_casts(self.vcx, vir_exprs.into_iter());
                Ok(sl.field_snaps_to_snap.apply(
                    self.vcx,
                    ty.ty_args.iter().map(|a| a.expr(self.vcx)),
                    casted_args,
                ))
            }
            SymValueKind::Projection(elem, base) => {
                let expr = self.encode_sym_value(deps, base, in_old)?;
                let ty = base.ty(self.vcx.tcx());
                match elem {
                    ProjectionElem::Deref => {
                        let e_ty = deps
                            .require_local::<RustTySnapshotsEnc>(ty.rust_ty())
                            .unwrap()
                            .generic_snapshot
                            .specifics
                            .get_structlike()
                            .ok_or(format!("expected struct-like, got {:?}", ty))?;
                        let expr = e_ty.field_access[0].read.apply(self.vcx, [expr]);
                        // Since the `expr` is the target of a reference, it is encoded as a `Param`.
                        // If it is not a type parameter, we cast it to its concrete Snapshot.
                        let rust_ty = sym_value.ty(self.vcx.tcx()).rust_ty();
                        let cast = deps
                            .require_local::<RustTyCastersEnc<CastTypePure>>(rust_ty)
                            .unwrap();
                        let casted = cast.cast_to_concrete_if_possible(self.vcx, expr);
                        Ok(casted)
                    }
                    ProjectionElem::Downcast(..) => Ok(expr),
                    ProjectionElem::Field(field_idx, field_ty) => {
                        let ty_out = deps
                            .require_local::<RustTySnapshotsEnc>(ty.rust_ty())
                            .unwrap();
                        let proj_fn = match ty_out.generic_snapshot.specifics {
                            domain::DomainEncSpecifics::StructLike(dds) => {
                                dds.field_access[usize::from(*field_idx)].read
                            }
                            domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                                if let Some(idx) = ty.variant_index() {
                                    let idx: usize = idx.into();
                                    de.variants[idx].fields.field_access[usize::from(*field_idx)]
                                        .read
                                } else {
                                    unreachable!(
                                        "Ty {:?} is an enumlike, but no variant idx is set",
                                        ty
                                    );
                                    // de.variants[0].fields.field_access[usize::from(*field_idx)].read
                                }
                            }
                            _ => todo!("projection to {:?}", ty_out.generic_snapshot.specifics),
                        };
                        let proj_app = proj_fn.apply(self.vcx, [expr]);
                        match ty.rust_ty().kind() {
                            ty::TyKind::Closure(_def_id, _substs) => {
                                let generic_cast = deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*field_ty)
                                    .unwrap();
                                Ok(generic_cast.cast_to_concrete_if_possible(self.vcx, proj_app))
                            }
                            ty::TyKind::Adt(def, _substs) => {
                                // The ADT type for the field might be generic, concretize if necessary
                                let variant =
                                    def.variant(ty.variant_index().unwrap_or(FIRST_VARIANT));
                                let generic_field_ty = variant.fields[*field_idx].ty(
                                    self.vcx.tcx(),
                                    GenericArgs::identity_for_item(self.vcx.tcx(), def.did()),
                                );
                                let cast_args = CastArgs {
                                    expected: *field_ty,      //  S<i32>
                                    actual: generic_field_ty, // T
                                };
                                Ok(deps
                                    .require_ref::<CastToEnc<CastTypePure>>(cast_args)
                                    .unwrap()
                                    .apply_cast_if_necessary(self.vcx, proj_app))
                            }
                            ty::TyKind::Tuple(_) => {
                                let generic_cast = deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*field_ty)
                                    .unwrap();
                                Ok(generic_cast.cast_to_concrete_if_possible(self.vcx, proj_app))
                            }
                            _ => Ok(proj_app),
                        }
                    }
                    _ => todo!(),
                }
            }
            SymValueKind::Discriminant(expr) => {
                let base = self.encode_sym_value(deps, expr, in_old)?;
                let ty = deps
                    .require_local::<RustTySnapshotsEnc>(expr.ty(self.vcx.tcx()).rust_ty())
                    .unwrap();
                match ty.generic_snapshot.specifics {
                    domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                        Ok(de.snap_to_discr_snap.apply(self.vcx, [base]))
                    }
                    other => panic!("discriminant of {:?}", other),
                }
            }
            SymValueKind::Ref(e, mutability) => self.encode_ref(deps, e, *mutability),
            SymValueKind::Synthetic(PrustiSymValSyntheticData::VirLocal(name, ty)) => {
                let ty = deps.require_local::<RustTySnapshotsEnc>(*ty).unwrap();
                Ok(self.vcx.mk_local_ex(
                    vir::vir_format!(self.vcx, "{}", name),
                    ty.generic_snapshot.snapshot,
                ))
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::PureFnCall(
                fn_def_id,
                substs,
                args,
            )) => self.encode_fn_call(deps, *fn_def_id, substs, args),
            SymValueKind::Synthetic(PrustiSymValSyntheticData::And(lhs, rhs)) => {
                let lhs = self.encode_sym_value_as_prim(deps, lhs)?;
                let rhs = self.encode_sym_value_as_prim(deps, rhs)?;
                let raw = self.vcx.mk_bin_op_expr(vir::BinOpKind::And, lhs, rhs);
                if let domain::DomainEncSpecifics::Primitive(dd) = deps
                    .require_local::<RustTySnapshotsEnc>(self.vcx.tcx().types.bool)
                    .unwrap()
                    .generic_snapshot
                    .specifics
                {
                    Ok(dd.prim_to_snap.apply(self.vcx, [raw]))
                } else {
                    unreachable!()
                }
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::If(cond, lhs, rhs)) => {
                let cond: vir::Expr<'vir> = self.encode_sym_value_as_prim(deps, cond)?;
                let lhs: vir::Expr<'vir> = self.encode_sym_value(deps, lhs, in_old)?;
                let rhs: vir::Expr<'vir> = self.encode_sym_value(deps, rhs, in_old)?;
                Ok(self.vcx.mk_ternary_expr(cond, lhs, rhs))
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::Old(value)) => {
                self.encode_sym_value(deps, value, true)
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::Result(ty)) => {
                let ty = deps.require_local::<RustTySnapshotsEnc>(*ty).unwrap();
                Ok(self.vcx.mk_result(ty.generic_snapshot.snapshot))
            }
            SymValueKind::Cast(_, operand, ty) => {
                let prim_val = self.encode_sym_value_as_prim(deps, operand)?;
                if let domain::DomainEncSpecifics::Primitive(dd) = deps
                    .require_local::<RustTySnapshotsEnc>(*ty)
                    .unwrap()
                    .generic_snapshot
                    .specifics
                {
                    Ok(dd.prim_to_snap.apply(self.vcx, [prim_val]))
                } else {
                    unreachable!()
                }
                // TODO: Make this more robust
            }
            SymValueKind::InternalError(err, _) => Err(format!("Encountered internal err {}", err)),
            SymValueKind::BackwardsFn(backwards_fn) => {
                self.encode_backwards_fn_call(deps, backwards_fn)
            }
        }
    }

    pub fn encode_sym_value_as_prim<'slf, 'enc, T: TaskEncoder<EncodingError = String>>(
        &'slf self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        expr: PrustiSymValue<'sym, 'tcx>,
    ) -> EncodeSymValueResult<'vir, String>
    where
        T: 'vir,
        EncodeFullError<'vir, T>: 'vir,
    {
        match &expr.kind {
            SymValueKind::Constant(c) => {
                if let Some(b) = c.as_bool(self.vcx.tcx()) {
                    if b {
                        return Ok(self.vcx.mk_bool::<true, !, !>());
                    } else {
                        return Ok(self.vcx.mk_bool::<false, !, !>());
                    }
                }
            }
            _ => {}
        }
        let generic_snapshot = deps
            .require_local::<RustTySnapshotsEnc>(expr.ty(self.vcx.tcx()).rust_ty())
            .unwrap()
            .generic_snapshot;
        let snap_to_prim = match generic_snapshot.specifics {
            domain::DomainEncSpecifics::Primitive(dd) => dd.snap_to_prim,
            _ => unreachable!(),
        };
        let expr: vir::Expr<'vir> = self.encode_sym_value(deps, expr, false)?;
        Ok(snap_to_prim.apply(self.vcx, [expr]))
    }

    fn encode_pc_atom<T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        pc: &PrustiPathConditionAtom<'sym, 'tcx>,
    ) -> EncodePCAtomResult<'vir, String> {
        match &pc {
            PathConditionAtom::Assertion(a) => {
                let encoder = AssertionEncoder::new(self.vcx, &self);
                let clauses = encoder.encode_assertion_clauses(deps, a);
                Ok(EncodedPCAtom::new(self.vcx.alloc_slice(&clauses)))
            }
            PathConditionAtom::Predicate(pc) => self.encode_pc_predicate_atom(deps, pc),
            PathConditionAtom::Not(pc) => match self.encode_path_condition(deps, pc) {
                Ok(pc) => Ok(EncodedPCAtom::singleton(
                    self.vcx
                        .mk_unary_op_expr(vir::UnOpKind::Not, pc.to_expr(self.vcx)),
                    self.vcx,
                )),
                Err(err) => Err(err),
            },
        }
    }

    fn encode_pc_predicate_atom<T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        pc: &PathConditionPredicateAtom<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
    ) -> EncodePCAtomResult<'vir, String> {
        let result = match &pc.predicate {
            PathConditionPredicate::ImpliedBy(pcs) => {
                let pcs = self.encode_path_condition(deps, &pcs).unwrap();
                Ok(EncodedPCAtom::singleton(
                    pcs.conditionalize_expr(
                        self.vcx,
                        self.encode_sym_value_as_prim(deps, &pc.expr)?,
                    ),
                    self.vcx,
                ))
            }
            PathConditionPredicate::Postcondition {
                def_id,
                substs,
                pre_values,
                post_values,
            } => {
                let args = post_values.iter().copied().chain(std::iter::once(pc.expr));
                let arg_substs = self.arena.alloc(Substs::from_iter(
                    args.enumerate().map(|(i, v)| (SymVar::nth_input(i), v)),
                ));
                let encoded_posts = deps
                    .require_local::<SymSpecEnc>((*def_id, substs, None))
                    .unwrap()
                    .posts
                    .into_iter()
                    .map(|p| {
                        self.with_old_values(BTreeMap::from_iter(
                            pre_values
                                .iter()
                                .enumerate()
                                .map(|(i, v)| (mir::Local::from_usize(i + 1), *v)),
                        ))
                        .encode_pure_spec(deps, p.subst(&self.arena, &arg_substs))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let clauses = encoded_posts
                    .into_iter()
                    .flat_map(|e| e.clauses)
                    .collect::<Vec<_>>();
                Ok::<EncodedPCAtom, String>(EncodedPCAtom::new(self.vcx.alloc_slice(&clauses)))
            }
            PathConditionPredicate::Eq(target, ty) => {
                // Optimization for booleans
                if *ty == self.vcx.tcx().types.bool {
                    let expr = self.encode_sym_value_as_prim(deps, &pc.expr)?;
                    if *target == 0 {
                        Ok(EncodedPCAtom::singleton(
                            self.vcx.mk_unary_op_expr(vir::UnOpKind::Not, expr),
                            self.vcx,
                        ))
                    } else {
                        Ok(EncodedPCAtom::singleton(expr, self.vcx))
                    }
                } else {
                    let expr = self.encode_sym_value(deps, &pc.expr, false)?;
                    Ok(EncodedPCAtom::singleton(
                        self.vcx
                            .mk_eq_expr(expr, self.encode_target_literal(deps, *target, *ty)),
                        self.vcx,
                    ))
                }
            }
            PathConditionPredicate::Ne(targets, ty) => {
                if *ty == self.vcx.tcx().types.bool {
                    let expr = self.encode_sym_value_as_prim(deps, &pc.expr)?;
                    if targets[0] == 1 {
                        return Ok(EncodedPCAtom::singleton(
                            self.vcx.mk_unary_op_expr(vir::UnOpKind::Not, expr),
                            self.vcx,
                        ));
                    } else {
                        return Ok(EncodedPCAtom::singleton(expr, self.vcx));
                    }
                }
                let expr = self.encode_sym_value(deps, &pc.expr, false)?;
                Ok(EncodedPCAtom::new(
                    self.vcx.alloc_slice(
                        &targets
                            .iter()
                            .map(|t| {
                                self.vcx.mk_unary_op_expr(
                                    vir::UnOpKind::Not,
                                    self.vcx.mk_eq_expr(
                                        expr,
                                        self.encode_target_literal(deps, *t, *ty),
                                    ),
                                )
                            })
                            .collect::<Vec<_>>(),
                    ),
                ))
            }
        }?;
        Ok(result)
    }

    fn encode_target_literal<T: TaskEncoder>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        target: u128,
        ty: ty::Ty<'tcx>,
    ) -> vir::Expr<'vir> {
        deps.require_local::<ConstEnc>((
            mir::Const::from_scalar(self.vcx.tcx(), Scalar::from_u128(target), ty),
            0,
            self.def_id,
        ))
        .unwrap()
    }

    // TODO: Should this include WF conditions?
    pub fn encode_pure_body<T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        spec: &SymPureEncResult<'sym, 'tcx>,
    ) -> EncodePureSpecResult<'vir, String> {
        let mut iter = spec.paths.iter();
        let mut expr = self.encode_sym_value(deps, &iter.next().unwrap().1, false)?;
        while let Some((pc, value)) = iter.next() {
            let encoded_value = self.encode_sym_value(deps, &value, false).unwrap();
            let pc = self.encode_path_condition(deps, pc).unwrap();
            expr = self
                .vcx
                .mk_ternary_expr(pc.to_expr(self.vcx), encoded_value, expr);
        }
        Ok(EncodedPureSpec {
            clauses: vec![expr],
        })
    }

    pub fn encode_pure_spec<'slf, 'enc, T: TaskEncoder<EncodingError = String>>(
        &'slf self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        spec: SymPureEncResult<'sym, 'tcx>,
    ) -> EncodePureSpecResult<'vir, String> {
        let path_clauses = spec
            .paths
            .into_iter()
            .map(|(pc, value)| {
                let encoded_value: vir::Expr<'vir> =
                    self.encode_sym_value_as_prim(deps, value).unwrap();
                self.encode_path_condition(deps, &pc)
                    .unwrap()
                    .conditionalize_expr(self.vcx, encoded_value)
            })
            .collect::<Vec<_>>();
        let well_formed_clauses = spec
            .well_formed
            .into_iter()
            .map(|ra| {
                let pcs = self.encode_path_condition(deps, &ra.pcs).unwrap();
                let assertion_encoder = AssertionEncoder::new(self.vcx, &self);
                pcs.conditionalize_expr(
                    self.vcx,
                    self.vcx.mk_disj(self.vcx.alloc_slice(
                        &assertion_encoder.encode_assertion_clauses(deps, &ra.assertion),
                    )),
                )
            })
            .collect::<Vec<_>>();
        let clauses = path_clauses
            .into_iter()
            .chain(well_formed_clauses.into_iter())
            .collect::<Vec<_>>();
        Ok(EncodedPureSpec { clauses })
    }

    pub fn encode_path_condition<T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        pc: &PrustiPathConditions<'sym, 'tcx>,
    ) -> EncodePCResult<'vir, String> {
        let mut exprs = Vec::new();
        for atom in &pc.atoms {
            let encoded = self.encode_pc_atom(deps, atom);
            match encoded {
                Ok(encoded) => exprs.push(encoded),
                Err(err) => return Err(err),
            }
        }
        Ok(EncodedPC { atoms: exprs })
    }
}

pub struct EncodedPCAtom<'vir> {
    clauses: &'vir [vir::Expr<'vir>],
}

impl<'vir> EncodedPCAtom<'vir> {
    pub fn new(clauses: &'vir [vir::Expr<'vir>]) -> Self {
        Self { clauses }
    }
    pub fn singleton(clause: vir::Expr<'vir>, vcx: &'vir vir::VirCtxt<'_>) -> Self {
        Self {
            clauses: vcx.alloc_slice(&[clause]),
        }
    }
    pub fn false_(vcx: &'vir vir::VirCtxt<'_>) -> Self {
        Self {
            clauses: vcx.alloc_slice(&[vcx.mk_bool::<false, !, !>()]),
        }
    }
    pub fn to_expr(&self, vcx: &'vir vir::VirCtxt<'_>) -> vir::Expr<'vir> {
        vcx.mk_conj(self.clauses)
    }
}

pub struct EncodedPC<'vir> {
    pub atoms: Vec<EncodedPCAtom<'vir>>,
}

impl<'vir> EncodedPC<'vir> {
    pub fn is_true(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn to_expr(&self, vcx: &'vir vir::VirCtxt<'_>) -> vir::Expr<'vir> {
        vcx.mk_conj(
            &self
                .atoms
                .iter()
                .flat_map(|atom| atom.clauses)
                .copied()
                .collect::<Vec<_>>(),
        )
    }

    pub fn conditionalize_expr(
        &self,
        vcx: &'vir vir::VirCtxt<'_>,
        expr: vir::Expr<'vir>,
    ) -> vir::Expr<'vir> {
        if self.is_true() {
            expr
        } else {
            vcx.mk_implies_expr(self.to_expr(vcx), expr)
        }
    }

    pub fn conditionalize_stmts(
        &self,
        vcx: &'vir vir::VirCtxt<'_>,
        stmts: Vec<vir::Stmt<'vir>>,
    ) -> Vec<vir::Stmt<'vir>> {
        if self.is_true() {
            return stmts;
        }
        vec![vcx.mk_if_stmt(self.to_expr(vcx), vcx.alloc_slice(&stmts), &[])]
    }
}
