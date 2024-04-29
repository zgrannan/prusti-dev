use mir_state_analysis::symbolic_execution::{
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    value::{Substs, SymValue},
    Assertion,
};
use prusti_rustc_interface::{
    abi,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
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

use crate::encoders::{ConstEnc, MirBuiltinEnc};

use super::{
    lifted::{
        cast::{CastArgs, PureGenericCastEnc},
        rust_ty_cast::RustTyGenericCastEnc,
    },
    mir_base::MirBaseEnc,
    mir_pure::PureKind,
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym_pure::SymPureEncResult,
    sym_spec::SymSpecEnc,
    MirBuiltinEncTask, SpecEnc, SpecEncTask, SymPureEnc, SymPureEncTask,
};

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
                vcx.tcx().item_name(def_id)
            );

            let method_ident = vir::MethodIdent::new(method_name, UnknownArity::new(&[]));

            deps.emit_output_ref::<SymImpureEnc>(
                *task_key,
                MirImpureEncOutputRef {
                    method_ref: method_ident,
                },
            );

            let body = vcx
                .body_mut()
                .get_impure_fn_body_identity(local_def_id)
                .body();

            let mut fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx());
            fpcs_analysis.analysis_for_bb(mir::START_BLOCK);
            let symbolic_execution = mir_state_analysis::run_symbolic_execution(
                &body,
                vcx.tcx(),
                mir_state_analysis::run_free_pcs(&body, vcx.tcx()),
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
            let spec = SymSpecEnc::encode(deps, (def_id, substs, caller_def_id));

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
            };

            let mut stmts = Vec::new();

            for local in symvar_locals.iter() {
                stmts.push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
            }
            stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            for pre in spec.pres {
                let pre = visitor.encode_pure_spec(&pre, None);
                stmts.push(vcx.mk_inhale_stmt(pre));
            }

            for (path, pcs, assertion) in symbolic_execution.assertions.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                let assertion = visitor.encode_assertion(assertion);
                if pcs.is_empty() {
                    stmts.push(assertion);
                } else {
                    let if_stmt = vcx.mk_if_stmt(
                        visitor.encode_path_condition(pcs),
                        vcx.alloc_slice(&[assertion]),
                        &[],
                    );
                    stmts.push(if_stmt);
                }
            }
            for (path, pcs, expr) in symbolic_execution.paths.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                let assertions: Vec<_> = spec
                    .posts
                    .iter()
                    .map(|p| {
                        visitor.encode_pure_spec(p, Some(&std::iter::once((body.arg_count, expr.clone())).collect()))
                    })
                    .collect();
                let assertions = vcx.mk_exhale_stmt(vcx.mk_conj(
                    vcx.alloc(&assertions)
                ));
                if pcs.is_empty() {
                    stmts.push(assertions);
                } else {
                    let if_stmt = vcx.mk_if_stmt(
                        visitor.encode_path_condition(pcs),
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

struct EncVisitor<'tcx, 'vir, 'enc>
where
    'vir: 'enc,
{
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir>,
    def_id: DefId,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    symvars: Vec<vir::Expr<'vir>>,
}

impl<'tcx, 'vir, 'enc> MirBaseEnc<'tcx, 'vir, 'enc> for EncVisitor<'tcx, 'vir, 'enc> {
    fn get_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'tcx> {
        &self.local_decls[local]
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir> {
        self.deps
    }
}

impl<'tcx, 'vir, 'enc> EncVisitor<'tcx, 'vir, 'enc> {
    fn encode_sym_value(&mut self, sym_value: &SymValue<'tcx>) -> vir::Expr<'vir> {
        let result = match sym_value {
            SymValue::Var(idx, _) => self.symvars[*idx],
            SymValue::Constant(c) => self
                .deps
                .require_local::<ConstEnc>((c.literal(), 0, self.def_id))
                .unwrap(),
            SymValue::CheckedBinaryOp(res_ty, op, lhs, rhs) => {
                let l_ty = lhs.ty(self.vcx.tcx()).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx()).rust_ty();
                let lhs = self.encode_sym_value(lhs);
                let rhs = self.encode_sym_value(rhs);
                let viper_fn = self
                    .deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::CheckedBinOp(
                        *res_ty, *op, l_ty, r_ty,
                    ))
                    .unwrap()
                    .function;
                viper_fn.apply(self.vcx, &[lhs, rhs])
            }
            SymValue::BinaryOp(res_ty, op, lhs, rhs) => {
                let l_ty = lhs.ty(self.vcx.tcx()).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx()).rust_ty();
                let lhs = self.encode_sym_value(lhs);
                let rhs = self.encode_sym_value(rhs);
                let viper_fn = self
                    .deps
                    .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::BinOp(
                        *res_ty, *op, l_ty, r_ty,
                    ))
                    .unwrap()
                    .function;
                viper_fn.apply(self.vcx, &[lhs, rhs])
            }
            SymValue::Aggregate(kind, exprs) => {
                let exprs = exprs
                    .iter()
                    .map(|e| self.encode_sym_value(e))
                    .collect::<Vec<_>>();
                let ty = self
                    .deps
                    .require_local::<RustTySnapshotsEnc>(kind.ty().rust_ty())
                    .unwrap();
                match ty.generic_snapshot.specifics {
                    super::domain::DomainEncSpecifics::StructLike(dds) => {
                        dds.field_snaps_to_snap.apply(self.vcx, &exprs)
                    }
                    super::domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                        if let Some(variant_idx) = sym_value.ty(self.vcx.tcx()).variant_index() {
                            let variant_idx: usize = variant_idx.into();
                            de.variants[variant_idx]
                                .fields
                                .field_snaps_to_snap
                                .apply(self.vcx, &exprs)
                        } else {
                            panic!("{:?} doesn't have a variant idx", sym_value);
                        }
                    }
                    _ => todo!("TODO: composition for {:?}", ty.generic_snapshot.specifics),
                }
            }
            SymValue::Projection(elem, base) => {
                let expr = self.encode_sym_value(base);
                let ty = base.ty(self.vcx.tcx());
                match elem {
                    ProjectionElem::Deref => {
                        todo!()
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
                        let proj_app = proj_fn.apply(self.vcx, [expr]);
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
                                eprintln!(
                                    "CASTING {:?} to {:?} for {:?}",
                                    *field_ty, generic_field_ty, def
                                );
                                self.deps
                                    .require_ref::<PureGenericCastEnc>(cast_args)
                                    .unwrap()
                                    .apply_cast_if_necessary(self.vcx, proj_app)
                            }
                            ty::TyKind::Tuple(_) => {
                                let generic_cast = self
                                    .deps
                                    .require_local::<RustTyGenericCastEnc>(*field_ty)
                                    .unwrap();
                                generic_cast.cast_to_concrete_if_possible(self.vcx, proj_app)
                            }
                            _ => proj_app,
                        }
                    }
                    _ => todo!(),
                }
            }
            SymValue::Discriminant(expr) => {
                let base = self.encode_sym_value(expr);
                let ty = self
                    .deps
                    .require_local::<RustTySnapshotsEnc>(expr.ty(self.vcx.tcx()).rust_ty())
                    .unwrap();
                match ty.generic_snapshot.specifics {
                    super::domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                        de.snap_to_discr_snap.apply(self.vcx, [base])
                    }
                    _ => unreachable!(),
                }
            }
            SymValue::Ref(_) => todo!(),
        };
        result
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

    fn encode_pc(&mut self, pc: &PathConditionAtom<'tcx>) -> vir::Expr<'vir> {
        let expr = self.encode_sym_value(&pc.expr);
        match &pc.predicate {
            PathConditionPredicate::Postcondition(def_id, args) => {
                let mut args = args.clone();
                args.push(pc.expr.clone());
                let mut encoded_posts = SymSpecEnc::encode(
                    self.deps,
                    (
                        *def_id,
                        ty::List::identity_for_item(self.vcx.tcx(), *def_id),
                        None,
                    ),
                )
                .posts
                .into_iter()
                .map(|p| {
                    self.encode_pure_spec(&p, Some(&args.iter().cloned().enumerate().collect()))
                })
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
                    let body = SymPureEnc::encode(SymPureEncTask {
                        kind: PureKind::Pure,
                        parent_def_id: *def_id,
                        param_env: self.vcx.tcx().param_env(*def_id),
                        substs: ty::List::identity_for_item(self.vcx.tcx(), *def_id),
                        caller_def_id: None, // TODO
                    });
                    for (path, value) in body.iter() {
                        encoded_posts.push(self.vcx.mk_implies_expr(
                            self.encode_path_condition(path),
                            self.vcx.mk_eq_expr(
                                self.encode_sym_value(&pc.expr),
                                self.encode_sym_value(&value.clone().subst(
                                    self.vcx.tcx(),
                                    &args.iter().cloned().enumerate().collect(),
                                )),
                            ),
                        ));
                    }
                }
                self.vcx.mk_conj(&encoded_posts)
            }
            PathConditionPredicate::Eq(target, ty) => self
                .vcx
                .mk_eq_expr(expr, self.encode_target_literal(*target, *ty)),
            PathConditionPredicate::Ne(targets, ty) => self.vcx.mk_conj(
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
            ),
        }
    }

    fn encode_sym_value_as_prim(&mut self, expr: &SymValue<'tcx>) -> vir::Expr<'vir> {
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
        eprintln!("Expr is {:?}", expr);
        eprintln!("Symvars: {:?}", self.symvars);
        snap_to_prim.apply(self.vcx, [self.encode_sym_value(expr)])
    }

    fn encode_pure_spec(
        &mut self,
        spec: &SymPureEncResult<'tcx>,
        substs: Option<&Substs<'tcx>>,
    ) -> vir::Expr<'vir> {
        let clauses = spec
            .iter()
            .map(|(pc, value)| {
                let encoded_pc = self.encode_path_condition(pc);
                let value = if let Some(substs) = substs {
                    value.clone().subst(self.vcx.tcx(), substs)
                } else {
                    value.clone()
                };
                let encoded_value = self.encode_sym_value_as_prim(&value);
                self.vcx.mk_implies_expr(encoded_pc, encoded_value)
            })
            .collect::<Vec<_>>();
        self.vcx.mk_conj(&clauses)
    }

    fn encode_assertion(&mut self, assertion: &Assertion<'tcx>) -> vir::Stmt<'vir> {
        let expr = match assertion {
            Assertion::Precondition(def_id, args) => {
                let encoded_pres = SymSpecEnc::encode(
                    self.deps,
                    (
                        *def_id,
                        ty::List::identity_for_item(self.vcx.tcx(), *def_id),
                        None,
                    ),
                )
                .pres
                .into_iter()
                .map(|p| {
                    self.encode_pure_spec(&p, Some(&args.iter().cloned().enumerate().collect()))
                })
                .collect::<Vec<_>>();
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

    fn encode_path_condition(&mut self, pc: &PathConditions<'tcx>) -> vir::Expr<'vir> {
        let mut exprs = Vec::new();
        for atom in &pc.atoms {
            exprs.push(self.encode_pc(&atom));
        }
        self.vcx.mk_conj(&exprs)
    }
}
