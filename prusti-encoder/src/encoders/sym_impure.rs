use std::marker::PhantomData;

use mir_state_analysis::symbolic_execution::{
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    value::{Substs, SymValueData, SymValueKind},
    Assertion, SymExArena,
};
use prusti_rustc_interface::{
    abi,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, MethodIdent, UnknownArity};

pub struct SymImpureEnc;

#[derive(Clone, Debug)]
pub enum MirImpureEncError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirImpureEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

use crate::encoders::{
    lifted::{cast::CastToEnc, casters::CastTypePure},
    ConstEnc, MirBuiltinEnc,
};

use super::{
    lifted::{
        cast::CastArgs, func_app_ty_params::LiftedFuncAppTyParamsEnc,
        rust_ty_cast::RustTyCastersEnc,
    },
    mir_base::MirBaseEnc,
    mir_pure::PureKind,
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym_pure::{
        PrustiPathConditions, PrustiSemantics, PrustiSubsts, PrustiSymValSynthetic,
        PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult,
    },
    sym_spec::SymSpecEnc,
    FunctionCallTaskDescription, MirBuiltinEncTask, PureFunctionEnc, SpecEnc, SpecEncTask,
    SymFunctionEnc, SymPureEnc, SymPureEncTask,
};

type PrustiPathConditionAtom<'sym, 'tcx> =
    PathConditionAtom<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
type PrustiAssertion<'sym, 'tcx> = Assertion<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

impl TaskEncoder for SymImpureEnc {
    task_encoder::encoder_cache!(SymImpureEnc);

    // TODO: local def id (+ promoted, substs, etc)
    type TaskDescription<'tcx> = (
        LocalDefId,               // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
    );

    type OutputRef<'vir> = MirImpureEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirImpureEncOutput<'vir>;

    type EncodingError = MirImpureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        EncodeFullError<'vir, Self>,
    > {
        let (local_def_id, substs, caller_def_id) = *task_key;
        let def_id = local_def_id.to_def_id();

        vir::with_vcx(|vcx| {
            let extra: String = substs.iter().map(|s| format!("_{s}")).collect();

            let caller = caller_def_id
                .map(|id| format!("{}_{}", id.krate, id.index.index()))
                .unwrap_or_default();

            let method_name = vir::vir_format_identifier!(
                vcx,
                "m_{}{extra}_CALLER_{caller}",
                vcx.tcx().def_path_str(def_id)
            );

            let method_ident = vir::MethodIdent::new(method_name, UnknownArity::new(&[]));

            deps.emit_output_ref(
                *task_key,
                MirImpureEncOutputRef {
                    method_ref: method_ident,
                },
            )?;

            let body = vcx
                .body_mut()
                .get_impure_fn_body_identity(local_def_id)
                .body();

            let arena = SymExArena::new();

            let symbolic_execution = mir_state_analysis::run_symbolic_execution(
                &body,
                vcx.tcx(),
                mir_state_analysis::run_free_pcs(&body, vcx.tcx()),
                PrustiSemantics(PhantomData),
                &arena,
            );

            let symvar_locals = symbolic_execution
                .symvars
                .iter()
                .enumerate()
                .map(|(idx, ty)| {
                    vcx.mk_local(
                        vir_format!(vcx, "s{}", idx),
                        deps.require_ref::<RustTySnapshotsEnc>(*ty)
                            .unwrap()
                            .generic_snapshot
                            .snapshot,
                    )
                })
                .collect::<Vec<_>>();
            let result_local = vcx.mk_local(
                "res",
                deps.require_ref::<RustTySnapshotsEnc>(
                    body.body.local_decls.iter().next().unwrap().ty,
                )
                .unwrap()
                .generic_snapshot
                .snapshot,
            );
            let spec = SymSpecEnc::encode(&arena, deps, (def_id, substs, caller_def_id));

            let body = &body.body;
            let mut visitor = EncVisitor {
                vcx,
                deps,
                def_id,
                local_decls: &body.local_decls,
                symvars: symvar_locals
                    .iter()
                    .map(|local| vcx.mk_local_ex(local.name, local.ty))
                    .collect::<Vec<_>>(),
                arena: &arena,
            };

            let mut stmts = Vec::new();

            for local in symvar_locals.iter() {
                stmts.push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
            }
            stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            for pre in spec.pres.into_iter() {
                let pre = visitor.encode_pure_spec(&pre, None).unwrap();
                stmts.push(vcx.mk_inhale_stmt(pre));
            }

            for (path, pcs, assertion) in symbolic_execution.assertions.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                let assertion = visitor.encode_assertion(assertion);
                if pcs.is_empty() {
                    stmts.push(assertion);
                } else {
                    let if_stmt = vcx.mk_if_stmt(
                        visitor.encode_path_condition(pcs).unwrap(),
                        vcx.alloc_slice(&[assertion]),
                        &[],
                    );
                    stmts.push(if_stmt);
                }
            }
            for (path, pcs, expr) in symbolic_execution.paths.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));

                // Generate assertions ensuring that `expr` satisfies each
                // postcondition attached to the function definition
                let assertions: Vec<_> = spec
                    .posts
                    .iter()
                    .map(|p| {
                        // The postcondition may refer to `result`; in this case
                        // `expr` should be considered as the result. The
                        // postcondition is encoded as a fn taking all arguments
                        // of this function plus an extra argument corresponding
                        // Therefore, the symbolic value at argument `body.arg_count`
                        // corresponds to the spec's symbolic input argument.
                        visitor.encode_pure_spec(
                            p,
                            Some(arena.alloc(Substs::singleton(body.arg_count, expr))),
                        )
                        .unwrap_or_else(|err| {
                            panic!("Error when encoding the postcondition {:?} of {:?} for path {:?}: {}", p, def_id, path, err)
                        })
                    })
                    .collect();
                let assertions = vcx.mk_exhale_stmt(vcx.mk_conj(vcx.alloc(&assertions)));
                if pcs.is_empty() {
                    stmts.push(assertions);
                } else {
                    let if_stmt = vcx.mk_if_stmt(
                        visitor.encode_path_condition(pcs).unwrap(),
                        vcx.alloc_slice(&[assertions]),
                        &[],
                    );
                    stmts.push(if_stmt);
                }
            }

            Ok((
                MirImpureEncOutput {
                    method: vcx.mk_method(
                        method_ident,
                        &[],
                        &[],
                        &[],
                        &[],
                        Some(vcx.alloc_slice(&[vcx.mk_cfg_block(
                            &vir::CfgBlockLabelData::Start,
                            vcx.alloc_slice(&stmts),
                            &vir::TerminatorStmtGenData::Exit,
                        )])),
                    ),
                },
                (),
            ))
        })
    }
}

struct EncVisitor<'sym, 'tcx, 'vir, 'enc>
where
    'vir: 'enc,
{
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir, SymImpureEnc>,
    def_id: DefId,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    symvars: Vec<vir::Expr<'vir>>,
    arena: &'sym SymExArena,
}

impl<'vir, 'enc> MirBaseEnc<'vir, 'enc> for EncVisitor<'_, 'vir, 'vir, 'enc> {
    fn get_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'vir> {
        &self.local_decls[local]
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, SymImpureEnc> {
        self.deps
    }
}

type EncodeSymValueResult<'vir> = Result<vir::Expr<'vir>, String>;
type EncodePCAtomResult<'vir> = Result<vir::Expr<'vir>, String>;
type EncodePCResult<'vir> = Result<vir::Expr<'vir>, String>;
type EncodePureSpecResult<'vir> = Result<vir::Expr<'vir>, String>;

impl<'sym, 'tcx, 'vir: 'tcx, 'enc> EncVisitor<'sym, 'tcx, 'vir, 'enc> {
    fn encode_sym_value(
        &mut self,
        sym_value: &PrustiSymValue<'sym, 'tcx>,
    ) -> EncodeSymValueResult<'vir> {
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
                let exprs = exprs
                    .iter()
                    .map(|e| self.encode_sym_value(e).unwrap())
                    .collect::<Vec<_>>();
                let ty = self
                    .deps
                    .require_local::<RustTySnapshotsEnc>(kind.ty().rust_ty())
                    .unwrap();
                match ty.generic_snapshot.specifics {
                    super::domain::DomainEncSpecifics::StructLike(dds) => {
                        Ok(dds.field_snaps_to_snap.apply(self.vcx, &exprs))
                    }
                    super::domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                        if let Some(variant_idx) = sym_value.ty(self.vcx.tcx()).variant_index() {
                            let variant_idx: usize = variant_idx.into();
                            Ok(de.variants[variant_idx]
                                .fields
                                .field_snaps_to_snap
                                .apply(self.vcx, &exprs))
                        } else {
                            panic!("{:?} doesn't have a variant idx", sym_value);
                        }
                    }
                    _ => todo!("TODO: composition for {:?}", ty.generic_snapshot.specifics),
                }
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
                        let cast = self
                            .deps
                            .require_local::<RustTyCastersEnc<CastTypePure>>(
                                sym_value.ty(self.vcx.tcx()).rust_ty(),
                            )
                            .unwrap();
                        Ok(cast.cast_to_concrete_if_possible(self.vcx, expr))
                    }
                    ProjectionElem::Downcast(..) => expr,
                    ProjectionElem::Field(field_idx, field_ty) => {
                        let ty_out = self
                            .deps
                            .require_local::<RustTySnapshotsEnc>(ty.rust_ty())
                            .unwrap();
                        let proj_fn = match ty_out.generic_snapshot.specifics {
                            super::domain::DomainEncSpecifics::StructLike(dds) => {
                                dds.field_access[usize::from(*field_idx)].read
                            }
                            super::domain::DomainEncSpecifics::EnumLike(Some(de)) => {
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
                                    expected: *field_ty,
                                    actual: generic_field_ty,
                                };
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
                    super::domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                        Ok(de.snap_to_discr_snap.apply(self.vcx, [base]))
                    }
                    other => panic!("discriminant of {:?}", other),
                }
            }
            SymValueKind::Ref(ty, e) => {
                let base = self.encode_sym_value(e).unwrap();
                let cast = self
                    .deps
                    .require_local::<RustTyCastersEnc<CastTypePure>>(e.ty(self.vcx.tcx()).rust_ty())
                    .unwrap();
                let base = cast.cast_to_generic_if_necessary(self.vcx, base);
                let ty = self.deps.require_local::<RustTySnapshotsEnc>(*ty).unwrap();
                if let super::domain::DomainEncSpecifics::StructLike(s) =
                    ty.generic_snapshot.specifics
                {
                    Ok(s.field_snaps_to_snap
                        .apply(self.vcx, self.vcx.alloc(&vec![base])))
                } else {
                    unreachable!()
                }
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
                                .deps()
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
                let lhs = self.encode_sym_value(lhs)?;
                let rhs = self.encode_sym_value(rhs)?;
                Ok(self.vcx.mk_bin_op_expr(vir::BinOpKind::And, lhs, rhs))
            }
            SymValueKind::Synthetic(PrustiSymValSyntheticData::If(_, _, _)) => todo!(),
        }
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

    fn encode_pc_atom(
        &mut self,
        pc: &PrustiPathConditionAtom<'sym, 'tcx>,
    ) -> EncodePCAtomResult<'vir> {
        match &pc.predicate {
            PathConditionPredicate::Postcondition(def_id, substs, args) => {
                let args = args.iter().copied().chain(std::iter::once(pc.expr));
                let arg_substs = self.arena.alloc(Substs::from_iter(args.enumerate()));
                let mut encoded_posts =
                    SymSpecEnc::encode(self.arena, self.deps, (*def_id, substs, None))
                        .posts
                        .into_iter()
                        .map(|p| self.encode_pure_spec(&p, Some(arg_substs)).unwrap())
                        .collect::<Vec<_>>();
                let is_pure = self
                    .deps
                    .require_local::<SpecEnc>(SpecEncTask { def_id: *def_id })
                    .unwrap()
                    .pure;
                let trusted = crate::encoders::with_proc_spec(*def_id, |def_spec| {
                    def_spec.trusted.extract_inherit().unwrap_or_default()
                })
                .unwrap_or_default();
                if is_pure && !trusted {
                    let body = SymPureEnc::encode(
                        self.arena,
                        SymPureEncTask {
                            kind: PureKind::Pure,
                            parent_def_id: *def_id,
                            param_env: self.vcx.tcx().param_env(*def_id),
                            substs: ty::List::identity_for_item(self.vcx.tcx(), *def_id),
                            caller_def_id: None, // TODO
                        },
                    );
                    let expr = pc.expr.subst(self.arena, self.vcx.tcx(), &arg_substs);
                    for (path, value) in body.iter() {
                        encoded_posts.push(
                            self.vcx.mk_implies_expr(
                                self.encode_path_condition(&path.clone().subst(
                                    self.arena,
                                    self.vcx.tcx(),
                                    &arg_substs,
                                ))
                                .unwrap(),
                                self.vcx.mk_eq_expr(
                                    self.encode_sym_value(&expr).unwrap(),
                                    self.encode_sym_value(&value.subst(
                                        self.arena,
                                        self.vcx.tcx(),
                                        arg_substs,
                                    ))
                                    .unwrap(),
                                ),
                            ),
                        );
                    }
                }
                Ok(self.vcx.mk_conj(&encoded_posts))
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
        }
    }

    fn encode_sym_value_as_prim(&mut self, expr: &PrustiSymValue<'sym, 'tcx>) -> vir::Expr<'vir> {
        let snap_to_prim = match self
            .deps
            .require_local::<RustTySnapshotsEnc>(expr.ty(self.vcx.tcx()).rust_ty())
            .unwrap()
            .generic_snapshot
            .specifics
        {
            super::domain::DomainEncSpecifics::Primitive(dd) => dd.snap_to_prim,
            _ => unreachable!(),
        };
        snap_to_prim.apply(self.vcx, [self.encode_sym_value(expr).unwrap()])
    }

    fn encode_pure_spec(
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
                let encoded_pc = self.encode_path_condition(pc)?;
                let encoded_value = self.encode_sym_value_as_prim(&value);
                let impl_expr = self.vcx.mk_implies_expr(encoded_pc, encoded_value);
                Ok::<vir::Expr<'vir>, String>(impl_expr)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(self.vcx.mk_conj(&clauses))
    }

    fn encode_assertion(&mut self, assertion: &PrustiAssertion<'sym, 'tcx>) -> vir::Stmt<'vir> {
        let expr = match assertion {
            Assertion::Precondition(def_id, substs, args) => {
                let arg_substs = self
                    .arena
                    .alloc(Substs::from_iter(args.iter().copied().enumerate()));
                let encoded_pres =
                    SymSpecEnc::encode(self.arena, self.deps, (*def_id, substs, None))
                        .pres
                        .into_iter()
                        .map(|p| self.encode_pure_spec(&p, Some(arg_substs)))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                self.vcx.mk_conj(&encoded_pres)
            }
            Assertion::Eq(expr, val) => {
                let expr = self.encode_sym_value_as_prim(expr);
                if *val {
                    self.vcx.mk_eq_expr(expr, self.vcx.mk_bool::<true>())
                } else {
                    self.vcx.mk_eq_expr(expr, self.vcx.mk_bool::<false>())
                }
            }
        };
        self.vcx.mk_exhale_stmt(expr)
    }

    fn encode_path_condition(
        &mut self,
        pc: &PrustiPathConditions<'sym, 'tcx>,
    ) -> EncodePCResult<'vir> {
        let mut exprs = Vec::new();
        for atom in &pc.atoms {
            exprs.push(self.encode_pc_atom(atom).map_err(|err| {
                format!(
                    "Failed to encode pc atom {:?} for pc {:?}: {}",
                    atom, pc, err
                )
            })?);
        }
        Ok(self.vcx.mk_conj(&exprs))
    }
}
