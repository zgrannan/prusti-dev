use mir_state_analysis::{
    free_pcs::{CapabilityKind, FreePcsBasicBlock, FreePcsLocation, RepackOp},
    symbolic_execution::{
        path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
        value::SymValue,
        Assertion,
    },
    utils::Place,
    FpcsOutput,
};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, interpret::Scalar, BinOp, ConstantKind, ProjectionElem},
        ty,
    },
    span::def_id::DefId,
};
//use mir_ssa_analysis::{
//    SsaAnalysis,
//};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, CallableIdent, MethodIdent, UnknownArity};

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
    pub local_field: vir::Field<'vir>,
}

use crate::encoders::{
    CapabilityEnc, ConstEnc, MirBuiltinEnc, MirFunctionEnc, MirLocalDefEnc, MirSpecEnc, SnapshotEnc,
};

use super::{
    mir_base::MirBaseEnc, mir_pure::PureKind, sym_spec::SymSpecEnc, MirBuiltinEncTask, SpecEnc,
    SpecEncTask, SymPureEnc, SymPureEncTask,
};

const ENCODE_REACH_BB: bool = false;

impl TaskEncoder for SymImpureEnc {
    task_encoder::encoder_cache!(SymImpureEnc);

    // TODO: local def id (+ promoted, substs, etc)
    type TaskDescription<'tcx> = (
        DefId,                    // ID of the function
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
        let (def_id, substs, caller_def_id) = *task_key;

        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();

        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;
            let local_defs = deps.require_local::<MirLocalDefEnc>(*task_key).unwrap();

            let method_name = vir::vir_format!(vcx, "m_{}", local_defs.field.name);
            let args = vec![&vir::TypeData::Ref; local_defs.inputs.len()];
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let method_ref = MethodIdent::new(method_name, args);
            deps.emit_output_ref::<Self>(*task_key, MirImpureEncOutputRef { method_ref });

            let local_field = vcx.mk_field(
                vir::vir_format!(vcx, "{method_name}_local"),
                &vir::TypeData::Ref,
            );

            // Do not encode the method body if it is trusted
            let local_def_id = def_id.as_local().filter(|_| !trusted);

            let blocks = if let Some(local_def_id) = local_def_id {
                let locals = local_defs.locals.unwrap();

                // TODO: substs, caller_def_id
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body_identity(local_def_id);
                // let body = vcx.tcx.mir_promoted(local_def_id).0.borrow();

                let mut fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx());
                fpcs_analysis.analysis_for_bb(mir::START_BLOCK);
                let symbolic_execution = mir_state_analysis::run_symbolic_execution(
                    &body,
                    vcx.tcx(),
                    mir_state_analysis::run_free_pcs(&body, vcx.tcx()),
                );
                let mut start_stmts = Vec::new();
                let symvar_locals = symbolic_execution
                    .symvars
                    .iter()
                    .enumerate()
                    .map(|(idx, ty)| {
                        vcx.mk_local(
                            vir_format!(vcx, "s{}", idx),
                            deps.require_ref::<SnapshotEnc>(*ty).unwrap().snapshot,
                        )
                    })
                    .collect::<Vec<_>>();
                for (idx, local) in symvar_locals.iter().enumerate() {
                    let init_expr = if idx < local_defs.inputs.len() {
                        Some(local_defs.inputs[idx].pure_local_ex)
                    } else {
                        None
                    };
                    start_stmts
                        .push(vcx.mk_local_decl_stmt(vcx.mk_local_decl_local(local), init_expr));
                }
                let body = &body.body;

                //let ssa_analysis = SsaAnalysis::analyse(&body);

                let block_count = body.basic_blocks.len();

                // Local count for the Viper method:
                // - one for each basic block;
                // - one (`Ref`) for each non-argument, non-return local.
                // let _local_count = block_count + 1 * (body.local_decls.len() - arg_count);

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                // for (idx, local) in locals.iter_enumerated() {
                //     start_stmts
                //         .push(vcx.mk_local_decl_stmt(vcx.mk_local_decl_local(local.local), None));
                //     // if !initial_state[idx].is_unallocated() {
                //     //     start_stmts.push(
                //     //         vcx.mk_new_stmt(local.pure_local_ex, Some(&[local_defs.field.field]))
                //     //     );
                //     let idx = idx.as_usize().wrapping_sub(1);
                //     if idx < local_defs.inputs.len() {
                //         start_stmts.push(vcx.mk_pure_assign_stmt(
                //             local.pure_local_ex,
                //             local_defs.inputs[idx].pure_local_ex,
                //         ));
                //     }
                //     //}
                // }
                if ENCODE_REACH_BB {
                    start_stmts.extend((0..block_count).map(|block| {
                        let name = vir::vir_format!(vcx, "_reach_bb{block}");
                        vcx.mk_local_decl_stmt(
                            vir::vir_local_decl! { vcx; [name] : Bool },
                            Some(vcx.mk_todo_expr("false")),
                        )
                    }));
                }
                encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::Start),
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::End),
                ));

                let mut visitor = EncVisitor {
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    //ssa_analysis,
                    fpcs_analysis,
                    field: local_defs.field,
                    local_defs: locals,

                    tmp_ctr: 0,

                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                    symvars: symvar_locals
                        .iter()
                        .map(|local| vcx.mk_local_ex(local.name, local.ty))
                        .collect::<Vec<_>>(),
                };

                let mut end_stmts = Vec::new();
                // end_stmts.push(
                //     vcx.mk_pure_assign_stmt(local_defs.output.local_ex, visitor.heap[&mir::RETURN_PLACE])
                // );
                for (path, pcs, assertion) in symbolic_execution.assertions.iter() {
                    end_stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                    let assertion = visitor.encode_assertion(assertion);
                    if pcs.is_empty() {
                        end_stmts.push(assertion);
                    } else {
                        let if_stmt = vcx.mk_if_stmt(
                            visitor.encode_path_condition(pcs),
                            vcx.alloc_slice(&[assertion]),
                            &[],
                        );
                        end_stmts.push(if_stmt);
                    }
                }
                for (path, pcs, expr) in symbolic_execution.paths.iter() {
                    end_stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                    let expr = visitor.encode_sym_value(expr);
                    let assign_stmt =
                        vcx.mk_pure_assign_stmt(local_defs.output.pure_local_ex, expr);
                    if pcs.is_empty() {
                        end_stmts.push(assign_stmt);
                    } else {
                        let if_stmt = vcx.mk_if_stmt(
                            visitor.encode_path_condition(pcs),
                            vcx.alloc_slice(&[assign_stmt]),
                            &[],
                        );
                        end_stmts.push(if_stmt);
                    }
                }
                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    vcx.alloc_slice(&end_stmts),
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));
                Some(vcx.alloc_slice(&visitor.encoded_blocks))
            } else {
                None
            };

            let spec = deps
                .require_local::<MirSpecEnc>((def_id, substs, caller_def_id, false))
                .unwrap();
            let (spec_pres, spec_posts) = (spec.pres, spec.posts);

            let args: Vec<_> = local_defs
                .inputs
                .iter()
                .map(|arg| vcx.mk_local_decl(arg.local.name, arg.ty.snapshot))
                .collect();
            let rets =
                [vcx.mk_local_decl(local_defs.output.local.name, local_defs.output.ty.snapshot)];
            let mut pres: Vec<_> = vec![];
            //  local_defs.inputs.iter().flat_map(|input| {
            //     let qps = input.ty.ref_to_region_refs.values().map(|r| r.region_qp(vcx, input.local_ex, vcx.mk_write(), false));
            //     [input.impure_pred].into_iter().chain(qps)
            // }).collect();
            pres.extend(spec_pres);

            let mut posts = Vec::with_capacity(spec_posts.len() + 1);
            // posts.extend(local_defs.inputs.iter().flat_map(|input| {
            //     input.ty.ref_to_region_refs.values().map(|r| r.region_qp(vcx, input.local_ex, vcx.mk_write(), true))
            // }));
            // posts.push(local_defs.output.impure_pred);
            // posts.extend(lifetime_posts);
            posts.extend(spec_posts);

            Ok((
                MirImpureEncOutput {
                    method: vcx.mk_method(
                        method_name,
                        vcx.alloc_slice(&args),
                        vcx.alloc_slice(&rets),
                        vcx.alloc_slice(&pres),
                        vcx.alloc_slice(&posts),
                        blocks,
                    ),
                    local_field,
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
    //ssa_analysis: SsaAnalysis,
    fpcs_analysis: FpcsOutput<'enc, 'tcx>,
    field: crate::encoders::local_def::MirLocalFieldEncOutput<'vir>,
    local_defs: &'vir IndexVec<mir::Local, crate::encoders::local_def::LocalDef<'vir>>,
    symvars: Vec<vir::Expr<'vir>>,

    tmp_ctr: usize,

    // for the current basic block
    current_fpcs: Option<FreePcsBasicBlock<'tcx>>,

    current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    current_terminator: Option<vir::TerminatorStmt<'vir>>,

    encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
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
    fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
        self.current_stmts.as_mut().unwrap().push(stmt);
    }

    fn unreachable(&mut self) -> vir::TerminatorStmt<'vir> {
        self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
        self.vcx.mk_assume_false_stmt()
    }

    fn encode_sym_value(&mut self, sym_value: &SymValue<'tcx>) -> vir::Expr<'vir> {
        let result = match sym_value {
            SymValue::Var(local, _) => self.symvars[*local],
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
                    .require_local::<SnapshotEnc>(kind.ty().rust_ty())
                    .unwrap();
                match ty.specifics {
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
                    _ => todo!("TODO: composition for {:?}", ty.specifics),
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
                            .require_local::<SnapshotEnc>(ty.rust_ty())
                            .unwrap();
                        let field_idx: usize = usize::from(*field_idx);
                        let proj_fn = match ty_out.specifics {
                            super::domain::DomainEncSpecifics::StructLike(dds) => {
                                dds.field_access[field_idx].read
                            }
                            super::domain::DomainEncSpecifics::EnumLike(Some(de)) => {
                                if let Some(idx) = ty.variant_index() {
                                    let idx: usize = idx.into();
                                    de.variants[idx].fields.field_access[field_idx].read
                                } else {
                                    unreachable!()
                                }
                            }
                            _ => todo!("projection to {:?}", ty_out.specifics),
                        };
                        eprintln!("proj_fn for {:?}:  {:?}", elem, proj_fn);
                        proj_fn.apply(self.vcx, [expr])
                    }
                    _ => todo!(),
                }
            }
            SymValue::Discriminant(expr) => {
                let base = self.encode_sym_value(expr);
                let ty = self
                    .deps
                    .require_local::<SnapshotEnc>(expr.ty(self.vcx.tcx()).rust_ty())
                    .unwrap();
                match ty.specifics {
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
                let args = std::iter::once(pc.expr.clone())
                    .chain(args.iter().cloned())
                    .collect::<Vec<_>>();
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
                .map(|p| self.encode_sym_value_as_prim(&p.subst(&args)))
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
                    let post = SymValue::BinaryOp(
                        self.vcx.tcx().types.bool,
                        BinOp::Eq,
                        Box::new(pc.expr.clone()),
                        Box::new(body.subst(&args)),
                    );
                    encoded_posts.push(self.encode_sym_value_as_prim(&post));
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
            .require_local::<SnapshotEnc>(expr.ty(self.vcx.tcx()).rust_ty())
            .unwrap()
            .specifics
        {
            super::domain::DomainEncSpecifics::Primitive(dd) => dd.snap_to_prim,
            _ => unreachable!(),
        };
        snap_to_prim.apply(self.vcx, [self.encode_sym_value(expr)])
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
                .map(|p| self.encode_sym_value_as_prim(&p.subst(&args)))
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
        debug_assert!(pc.atoms.len() > 0);
        let mut exprs = Vec::new();
        for atom in &pc.atoms {
            exprs.push(self.encode_pc(&atom));
        }
        self.vcx.mk_conj(&exprs)
    }

    fn new_tmp(&mut self, ty: &'vir vir::TypeData<'vir>) -> (vir::Local<'vir>, vir::Expr<'vir>) {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        self.stmt(
            self.vcx
                .mk_local_decl_stmt(vir::vir_local_decl! { self.vcx; [name] : [ty] }, None),
        );
        let tmp = self.vcx.mk_local(name, ty);
        (tmp, self.vcx.mk_local_ex_local(tmp))
    }
}
