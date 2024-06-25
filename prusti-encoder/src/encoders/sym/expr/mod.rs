use prusti_rustc_interface::{
    abi,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::{PathConditionAtom, PathConditionPredicate},
    value::{AggregateKind, Substs, SymValueKind},
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};

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

mod r#ref;

type EncodePCResult<'vir> = Result<vir::Expr<'vir>, String>;
type EncodePureSpecResult<'vir> = Result<vir::Expr<'vir>, String>;
pub type EncodePCAtomResult<'vir> = Result<vir::Expr<'vir>, String>;
pub type EncodeSymValueResult<'vir> = Result<vir::Expr<'vir>, String>;
type PrustiPathConditionAtom<'sym, 'tcx> =
    PathConditionAtom<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

pub struct SymExprEncoder<'enc, 'vir: 'tcx, 'sym, 'tcx, T: TaskEncoder> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, T>,
    arena: &'sym SymExContext,
    symvars: Vec<vir::Expr<'vir>>,
    def_id: DefId,
}

impl<'enc, 'vir, 'sym, 'tcx, T: TaskEncoder> SymExprEncoder<'enc, 'vir, 'sym, 'tcx, T> {
    pub fn new(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        arena: &'sym SymExContext,
        symvars: Vec<vir::Expr<'vir>>,
        def_id: DefId,
    ) -> Self {
        Self {
            vcx,
            deps,
            arena,
            symvars,
            def_id,
        }
    }
    pub fn encode_sym_value(
        &mut self,
        sym_value: PrustiSymValue<'sym, 'tcx>,
    ) -> EncodeSymValueResult<'vir> {
        let sym_value = sym_value.optimize(self.arena, self.vcx.tcx());
        match &sym_value.kind {
            SymValueKind::Var(idx, ..) => self.symvars.get(*idx).cloned().ok_or_else(|| {
                panic!("{}", sym_value.debug_info);
                format!(
                    "No symvar at idx {}. The symvar was created via {}",
                    *idx, sym_value.debug_info
                )
            }),

            SymValueKind::Constant(c) => Ok(self
                .deps
                .require_local::<ConstEnc>((c.literal(), 0, self.def_id))
                .unwrap()),
            SymValueKind::CheckedBinaryOp(res_ty, op, lhs, rhs) => {
                let l_ty = lhs.ty(self.vcx.tcx()).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx()).rust_ty();
                let lhs = self.encode_sym_value(lhs)?;
                let rhs = self.encode_sym_value(rhs)?;
                let viper_fn = self
                    .deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::CheckedBinOp(
                        *res_ty, *op, l_ty, r_ty,
                    ))
                    .unwrap()
                    .function;
                Ok(viper_fn.apply(self.vcx, &[lhs, rhs]))
            }
            SymValueKind::BinaryOp(res_ty, op, lhs, rhs) => {
                let l_ty = lhs.ty(self.vcx.tcx()).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx()).rust_ty();
                let lhs = self.encode_sym_value(lhs)?;
                let rhs = self.encode_sym_value(rhs)?;
                let viper_fn = self
                    .deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::BinOp(
                        *res_ty, *op, l_ty, r_ty,
                    ))
                    .unwrap()
                    .function;
                Ok(viper_fn.apply(self.vcx, &[lhs, rhs]))
            }
            SymValueKind::UnaryOp(ty, op, expr) => {
                let expr = self.encode_sym_value(expr)?;
                let viper_fn = self
                    .deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::UnOp(*ty, *op, *ty))
                    .unwrap()
                    .function;
                Ok(viper_fn.apply(self.vcx, &[expr]))
            }
            SymValueKind::Aggregate(kind, exprs) => {
                if let AggregateKind::PCS(ty, _) = kind && ty.is_ref() {
                    return self.encode_ref(*ty, exprs[0]);
                }
                let vir_exprs = exprs
                    .iter()
                    .map(|e| self.encode_sym_value(e).unwrap())
                    .collect::<Vec<_>>();
                let ty = self
                    .deps
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
                    _ => ty.generic_snapshot.specifics.expect_structlike(),
                };
                let field_tys = exprs
                    .iter()
                    .map(|e| e.ty(self.vcx.tcx()).rust_ty())
                    .collect::<Vec<_>>();
                let ty_caster = self
                    .deps
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
                            other => todo!("aggregate kind {:?}", other),
                        },
                    })
                    .unwrap();
                let casted_args = ty_caster.apply_casts(self.vcx, vir_exprs.into_iter());
                Ok(sl
                    .field_snaps_to_snap
                    .apply(self.vcx, self.vcx.alloc_slice(&casted_args)))
            }
            SymValueKind::Projection(elem, base) => {
                let expr = self.encode_sym_value(base);
                let ty = base.ty(self.vcx.tcx());
                match elem {
                    ProjectionElem::Deref => {
                        let e_ty = self
                            .deps
                            .require_local::<RustTySnapshotsEnc>(ty.rust_ty())
                            .unwrap()
                            .generic_snapshot
                            .specifics
                            .expect_structlike();
                        let expr = e_ty.field_access[0].read.apply(self.vcx, [expr.unwrap()]);
                        // Since the `expr` is the target of a reference, it is encoded as a `Param`.
                        // If it is not a type parameter, we cast it to its concrete Snapshot.
                        let rust_ty = sym_value.ty(self.vcx.tcx()).rust_ty();
                        let cast = self
                            .deps
                            .require_local::<RustTyCastersEnc<CastTypePure>>(
                                rust_ty
                            )
                            .unwrap();
                        eprintln!("CAST: {:?}", rust_ty);
                        let casted = cast.cast_to_concrete_if_possible(self.vcx, expr);
                        eprintln!("CASTED {:?} to {:?}", expr, casted);
                        Ok(casted)
                    }
                    ProjectionElem::Downcast(..) => expr,
                    ProjectionElem::Field(field_idx, field_ty) => {
                        let ty_out = self
                            .deps
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
                                    unreachable!()
                                }
                            }
                            _ => todo!("projection to {:?}", ty_out.generic_snapshot.specifics),
                        };
                        let proj_app = proj_fn.apply(self.vcx, [expr.unwrap()]);
                        match ty.rust_ty().kind() {
                            ty::TyKind::Adt(def, _) => {
                                // The ADT type for the field might be generic, concretize if necessary
                                let variant =
                                    def.variant(ty.variant_index().unwrap_or(abi::FIRST_VARIANT));
                                let generic_field_ty = variant.fields[*field_idx].ty(
                                    self.vcx.tcx(),
                                    GenericArgs::identity_for_item(self.vcx.tcx(), def.did()),
                                );
                                let cast_args = CastArgs {
                                    expected: *field_ty, //  S<i32>
                                    actual: generic_field_ty, // T
                                };
                                eprintln!("ARGS: {:?}", cast_args);
                                Ok(self
                                    .deps
                                    .require_ref::<CastToEnc<CastTypePure>>(cast_args)
                                    .unwrap()
                                    .apply_cast_if_necessary(self.vcx, proj_app))
                            }
                            ty::TyKind::Tuple(_) => {
                                let generic_cast = self
                                    .deps
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
                let base = self.encode_sym_value(expr)?;
                let ty = self
                    .deps
                    .require_local::<RustTySnapshotsEnc>(expr.ty(self.vcx.tcx()).rust_ty())
                    .unwrap();
                match ty.generic_snapshot.specifics {
                    domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                        Ok(de.snap_to_discr_snap.apply(self.vcx, [base]))
                    }
                    other => panic!("discriminant of {:?}", other),
                }
            }
            SymValueKind::Ref(ty, e) => {
                self.encode_ref(*ty, e)
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::PureFnCall(
                fn_def_id,
                substs,
                args,
            )) => {
                let mono = cfg!(feature = "mono_function_encoding");
                let sig = self.vcx.tcx().fn_sig(fn_def_id);
                let sig = if mono {
                    let param_env = self.vcx.tcx().param_env(self.def_id);
                    self.vcx
                        .tcx()
                        .subst_and_normalize_erasing_regions(substs, param_env, sig)
                } else {
                    sig.instantiate_identity()
                };

                let fn_arg_tys = sig
                    .inputs()
                    .iter()
                    .map(|i| i.skip_binder())
                    .copied()
                    .collect::<Vec<_>>();
                let encoded_ty_args = self
                    .deps
                    .require_local::<LiftedFuncAppTyParamsEnc>((mono, substs))
                    .unwrap();
                let encoded_args = encoded_ty_args.iter().map(|ty| ty.expr(self.vcx));
                let encoded_fn_args =
                    fn_arg_tys
                        .into_iter()
                        .zip(args.iter())
                        .map(|(expected_ty, arg)| {
                            let base = self.encode_sym_value(arg).unwrap();
                            let arg_ty = arg.ty(self.vcx.tcx()).rust_ty();
                            let caster = self
                                .deps
                                .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                                    expected: expected_ty,
                                    actual: arg_ty,
                                })
                                .unwrap();
                            caster.apply_cast_if_necessary(self.vcx, base)
                        });
                let args = encoded_args.chain(encoded_fn_args).collect::<Vec<_>>();
                let function_ref = self
                    .deps
                    .require_ref::<SymFunctionEnc>(FunctionCallTaskDescription {
                        def_id: *fn_def_id,
                        substs: if mono {
                            substs
                        } else {
                            GenericArgs::identity_for_item(self.vcx.tcx(), *fn_def_id)
                        },
                        caller_def_id: self.def_id,
                    })
                    .unwrap()
                    .function_ident;
                Ok(function_ref.apply(self.vcx, &args))
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::And(lhs, rhs)) => {
                let lhs = self.encode_sym_value_as_prim(lhs);
                let rhs = self.encode_sym_value_as_prim(rhs);
                let raw = self.vcx.mk_bin_op_expr(vir::BinOpKind::And, lhs, rhs);
                if let domain::DomainEncSpecifics::Primitive(dd) = self
                    .deps
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
                let cond = self.encode_sym_value_as_prim(cond);
                let lhs = self.encode_sym_value(lhs)?;
                let rhs = self.encode_sym_value(rhs)?;
                Ok(self.vcx.mk_ternary_expr(cond, lhs, rhs))
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::Result(ty)) => {
                let ty = self.deps.require_local::<RustTySnapshotsEnc>(*ty).unwrap();
                Ok(self.vcx.mk_result(ty.generic_snapshot.snapshot))
            }
            SymValueKind::Cast(_, operand, ty) => {
                let prim_val = self.encode_sym_value_as_prim(operand);
                if let domain::DomainEncSpecifics::Primitive(dd) = self
                    .deps
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
            SymValueKind::InternalError(_, _) => todo!(),
        }
    }

    pub fn encode_sym_value_as_prim(
        &mut self,
        expr: &PrustiSymValue<'sym, 'tcx>,
    ) -> vir::Expr<'vir> {
        let snap_to_prim = match self
            .deps
            .require_local::<RustTySnapshotsEnc>(expr.ty(self.vcx.tcx()).rust_ty())
            .unwrap()
            .generic_snapshot
            .specifics
        {
            domain::DomainEncSpecifics::Primitive(dd) => dd.snap_to_prim,
            _ => unreachable!(),
        };
        snap_to_prim.apply(self.vcx, [self.encode_sym_value(expr).unwrap()])
    }

    fn encode_pc_atom(
        &mut self,
        pc: &PrustiPathConditionAtom<'sym, 'tcx>,
    ) -> EncodePCAtomResult<'vir> {
        let result = match &pc.predicate {
            PathConditionPredicate::Postcondition(def_id, substs, args) => {
                let args = args.iter().copied().chain(std::iter::once(pc.expr));
                let arg_substs = self.arena.alloc(Substs::from_iter(args.enumerate()));
                let encoded_posts =
                    SymSpecEnc::encode(self.arena, self.deps, (*def_id, substs, None))
                        .posts
                        .into_iter()
                        .map(|p| self.encode_pure_spec(&p, Some(arg_substs)).unwrap())
                        .collect::<Vec<_>>();
                Ok::<vir::Expr<'vir>, String>(self.vcx.mk_conj(&encoded_posts))
            }
            PathConditionPredicate::Eq(target, ty) => {
                let expr = self.encode_sym_value(&pc.expr)?;
                Ok(self
                    .vcx
                    .mk_eq_expr(expr, self.encode_target_literal(*target, *ty)))
            }
            PathConditionPredicate::Ne(targets, ty) => {
                let expr = self.encode_sym_value(&pc.expr)?;
                Ok(self.vcx.mk_conj(
                    &targets
                        .iter()
                        .map(|t| {
                            self.vcx.mk_unary_op_expr(
                                vir::UnOpKind::Not,
                                self.vcx
                                    .mk_eq_expr(expr, self.encode_target_literal(*t, *ty)),
                            )
                        })
                        .collect::<Vec<_>>(),
                ))
            }
        }?;
        assert_eq!(result.ty(), &vir::TypeData::Bool);
        Ok::<vir::Expr<'vir>, String>(result)
    }

    fn encode_target_literal(&mut self, target: u128, ty: ty::Ty<'tcx>) -> vir::Expr<'vir> {
        self.deps
            .require_local::<ConstEnc>((
                ConstantKind::from_scalar(self.vcx.tcx(), Scalar::from_u128(target), ty),
                0,
                self.def_id,
            ))
            .unwrap()
    }
    pub fn encode_pure_body(
        &mut self,
        spec: &SymPureEncResult<'sym, 'tcx>,
    ) -> EncodePureSpecResult<'vir> {
        let mut iter = spec.iter();
        let mut expr = self.encode_sym_value(&iter.next().unwrap().1).unwrap();
        while let Some((pc, value)) = iter.next() {
            let encoded_value = self.encode_sym_value(&value).unwrap();
            let pc = self.encode_path_condition(pc).unwrap().unwrap();
            expr = self.vcx.mk_ternary_expr(pc, encoded_value, expr);
        }
        Ok(expr)
    }

    pub fn encode_pure_spec(
        &mut self,
        spec: &SymPureEncResult<'sym, 'tcx>,
        substs: Option<&'sym PrustiSubsts<'sym, 'tcx>>,
    ) -> EncodePureSpecResult<'vir> {
        let spec = if let Some(substs) = substs {
            spec.clone().subst(self.arena, self.vcx.tcx(), substs)
        } else {
            spec.clone()
        };
        let clauses = spec
            .iter()
            .map(|(pc, value)| {
                let encoded_value = self.encode_sym_value_as_prim(&value);
                if let Some(pc) = self.encode_path_condition(pc) {
                    let impl_expr = self.vcx.mk_implies_expr(pc.unwrap(), encoded_value);
                    Ok::<vir::Expr<'vir>, String>(impl_expr)
                } else {
                    Ok::<vir::Expr<'vir>, String>(encoded_value)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(self.vcx.mk_conj(&clauses))
    }

    pub fn encode_path_condition(
        &mut self,
        pc: &PrustiPathConditions<'sym, 'tcx>,
    ) -> Option<EncodePCResult<'vir>> {
        if pc.atoms.is_empty() {
            return None;
        }
        let mut exprs = Vec::new();
        for atom in &pc.atoms {
            exprs.push(
                self.encode_pc_atom(atom)
                    .map_err(|err| {
                        format!(
                            "Failed to encode pc atom {:?} for pc {:?}: {}",
                            atom, pc, err
                        )
                    })
                    .unwrap(),
            );
        }
        Some(Ok(self.vcx.mk_conj(&exprs)))
    }
}
