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
                    .body
                    .borrow_mut()
                    .get_impure_fn_body_identity(local_def_id);
                // let body = vcx.tcx.mir_promoted(local_def_id).0.borrow();

                let mut fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx);
                fpcs_analysis.analysis_for_bb(mir::START_BLOCK);
                let symbolic_execution = mir_state_analysis::run_symbolic_execution(
                    &body,
                    vcx.tcx,
                    mir_state_analysis::run_free_pcs(&body, vcx.tcx),
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

                for (idx, local) in locals.iter().enumerate() {
                    debug_assert!(matches!(
                        local.pure_local_ex.ty(),
                        vir::TypeData::Domain(..)
                    ));
                }

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
                visitor.visit_body(&body);

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
                        let if_stmt = vcx.mk_if_stmt(visitor.encode_path_condition(pcs), assertion);
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
                        let if_stmt =
                            vcx.mk_if_stmt(visitor.encode_path_condition(pcs), assign_stmt);
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
                let l_ty = lhs.ty(self.vcx.tcx).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx).rust_ty();
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
                let l_ty = lhs.ty(self.vcx.tcx).rust_ty();
                let r_ty = rhs.ty(self.vcx.tcx).rust_ty();
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
                        if let Some(variant_idx) = sym_value.ty(self.vcx.tcx).variant_index() {
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
                let ty = base.ty(self.vcx.tcx);
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
                    .require_local::<SnapshotEnc>(expr.ty(self.vcx.tcx).rust_ty())
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
                ConstantKind::from_scalar(self.vcx.tcx, Scalar::from_u128(target), ty),
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
                        ty::List::identity_for_item(self.vcx.tcx, *def_id),
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
                        param_env: self.vcx.tcx.param_env(*def_id),
                        substs: ty::List::identity_for_item(self.vcx.tcx, *def_id),
                        caller_def_id: None, // TODO
                    });
                    let post = SymValue::BinaryOp(
                        self.vcx.tcx.types.bool,
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
            .require_local::<SnapshotEnc>(expr.ty(self.vcx.tcx).rust_ty())
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
                        ty::List::identity_for_item(self.vcx.tcx, *def_id),
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

    /// Do the same as [self.fpcs_repacks_terminator] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_terminator_repacks(
        &mut self,
        idx: usize,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) -> Vec<&'vir vir::StmtData<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.fpcs_repacks_terminator(idx, repacks);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    fn fpcs_repacks(&mut self, repacks: &[RepackOp<'tcx>]) {
        for &repack_op in repacks {
            match repack_op {
                RepackOp::Expand(place, _target, capability_kind)
                | RepackOp::Collapse(place, _target, capability_kind) => {
                    if matches!(capability_kind, CapabilityKind::Write) {
                        // Collapsing an already exhaled place is a no-op
                        // TODO: unless it's through a Ref I imagine?
                        assert!(matches!(repack_op, RepackOp::Collapse(..)));
                        return;
                    }
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx);
                    let place_ty_out = self.deps.require_ref::<CapabilityEnc>(place_ty.ty).unwrap();
                    let ref_to_pred = place_ty_out.expect_pred_variant_opt(place_ty.variant_index);

                    let ref_p = self.encode_place(place);
                    let predicate = ref_to_pred.apply(self.vcx, [ref_p], None);
                    if matches!(
                        repack_op,
                        mir_state_analysis::free_pcs::RepackOp::Expand(..)
                    ) {
                        self.stmt(self.vcx.mk_unfold_stmt(predicate));
                    } else {
                        self.stmt(self.vcx.mk_fold_stmt(predicate));
                    }
                }
                RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx);
                    assert!(place_ty.variant_index.is_none());

                    let place_ty_out = self.deps.require_ref::<CapabilityEnc>(place_ty.ty).unwrap();

                    let ref_p = self.encode_place(place);
                    // self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_predicate_app_expr(
                    //     place_ty_out.ref_to_pred.apply(self.vcx, [ref_p], None)
                    // )));
                }
                unsupported_op => panic!("unsupported repack op: {unsupported_op:?}"),
            }
        }
    }

    fn fpcs_repacks_location(
        &mut self,
        location: mir::Location,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let repacks = repacks(&current_fpcs.statements[location.statement_index]);
        self.fpcs_repacks(repacks);
        self.current_fpcs = Some(current_fpcs);
    }

    fn fpcs_repacks_terminator(
        &mut self,
        succ_idx: usize,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let repacks = repacks(&current_fpcs.terminator.succs[succ_idx]);
        self.fpcs_repacks(repacks);
        self.current_fpcs = Some(current_fpcs);
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'tcx>) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx);
        match operand {
            &mir::Operand::Move(source) => self.encode_place(Place::from(source)),
            &mir::Operand::Copy(source) => self.encode_place(Place::from(source)),
            mir::Operand::Constant(box constant) => self
                .deps
                .require_local::<ConstEnc>((constant.literal, 0, self.def_id))
                .unwrap(),
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'tcx>) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx);
        let (snap_val, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)),
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<CapabilityEnc>(ty).unwrap();
                let source = ty_out
                    .ref_to_snap
                    .apply(self.vcx, [self.encode_place(Place::from(source))]);
                (source, ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<CapabilityEnc>(ty).unwrap();
                let constant = self
                    .deps
                    .require_local::<ConstEnc>((constant.literal, 0, self.def_id))
                    .unwrap();
                (constant, ty_out)
            }
        };
        let tmp_exp = self.new_tmp(&vir::TypeData::Ref).1;
        self.stmt(
            self.vcx.alloc(
                ty_out
                    .method_assign
                    .apply(self.vcx, &[], [tmp_exp, snap_val]),
            ),
        );
        tmp_exp
    }

    fn encode_place_snap(
        &mut self,
        place: Place<'tcx>,
        ty: ty::Ty<'tcx>,
        perm: Option<vir::Expr<'vir>>,
    ) -> (vir::Expr<'vir>, vir::Expr<'vir>) {
        let ty_out = self.deps.require_ref::<CapabilityEnc>(ty).unwrap();
        let place_exp = self.encode_place(Place::from(place));
        let snap_val = ty_out.ref_to_snap.apply(self.vcx, [place_exp]);

        let tmp_exp = self.new_tmp(ty_out.snapshot).1;
        self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
        // self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_predicate_app_expr(
        //     ty_out.ref_to_pred.apply(self.vcx, [place_exp], perm)
        // )));
        (tmp_exp, place_exp)
    }

    fn encode_place(&mut self, place: Place<'tcx>) -> vir::Expr<'vir> {
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut expr = self.local_defs[place.local].pure_local_ex;
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            expr = self.encode_place_element(place_ty, elem, expr);
            place_ty = place_ty.projection_ty(self.vcx.tcx, elem);
        }
        expr
    }

    fn encode_place_element(
        &mut self,
        place_ty: mir::tcx::PlaceTy<'tcx>,
        elem: mir::PlaceElem<'tcx>,
        expr: vir::Expr<'vir>,
    ) -> vir::Expr<'vir> {
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self.deps.require_ref::<CapabilityEnc>(place_ty.ty).unwrap();
                let field_access = e_ty
                    .expect_variant_opt(place_ty.variant_index)
                    .ref_to_field_refs;
                let projection_p = field_access[field_idx.as_usize()];
                projection_p.apply(self.vcx, [expr])
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => expr,
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self.deps.require_ref::<CapabilityEnc>(place_ty.ty).unwrap();
                let ref_field = e_ty.expect_ref().ref_field;
                self.vcx.mk_field_expr(expr, ref_field)
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
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

impl<'tcx, 'vir, 'enc> mir::visit::Visitor<'tcx> for EncVisitor<'tcx, 'vir, 'enc> {
    // fn visit_body(&mut self, body: &mir::Body<'tcx>) {
    //     println!("visiting body!");
    // }
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'tcx>) {
        return;
        self.current_fpcs = Some(self.fpcs_analysis.get_all_for_bb(block));

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        if ENCODE_REACH_BB {
            self.stmt(self.vcx.mk_pure_assign_stmt(
                self.vcx.mk_local_ex(
                    vir::vir_format!(self.vcx, "_reach_bb{}", block.as_usize()),
                    &vir::TypeData::Bool,
                ),
                self.vcx.mk_bool::<true>(),
            ));
        }

        /*
        let mut phi_stmts = vec![];
        if let Some(phi_nodes) = self.ssa_analysis.phi.get(&block) {
            for phi_node in phi_nodes {
                assert!(!phi_node.sources.is_empty());
                let local_ty = &self.local_types[phi_node.local];
                let expr = phi_node.sources.iter()
                    .fold(self.vcx.mk_func_app(
                        local_ty.function_unreachable,
                        &[],
                    ), |prev, source| self.vcx.alloc(vir::ExprData::Ternary(self.vcx.alloc(vir::TernaryData {
                        cond: self.vcx.mk_local_ex(vir::vir_format!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(vir::vir_format!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: vir::vir_format!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
                    ty: self.local_types[phi_node.local].snapshot,
                    expr: Some(expr),
                })));
            }
        }
        for phi_stmt in phi_stmts {
            self.stmt(phi_stmt);
        }
        */

        assert!(self.current_terminator.is_none());
        self.super_basic_block_data(block, data);
        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
        self.encoded_blocks.push(
            self.vcx.mk_cfg_block(
                self.vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
                self.vcx.alloc_slice(&stmts),
                terminator,
            ),
        );
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>, location: mir::Location) {
        return;
        self.stmt(self.vcx.mk_comment_stmt(
            // TODO: also add bb and location for better debugging?
            vir::vir_format!(self.vcx, "{statement:?}"),
        ));

        self.fpcs_repacks_location(location, |loc| &loc.repacks_start);
        // TODO: move this to after getting operands, before assignment
        self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);
        match &statement.kind {
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                //let ssa_update = self.ssa_analysis.updates.get(&location).cloned().unwrap();
                //assert!(ssa_update.local == dest.local);

                //let old_name_s = vir::vir_format!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.old_version);
                //let name_s = vir::vir_format!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.new_version);
                //let ty_s = self.local_types[ssa_update.local].snapshot;

                // What are we assigning to?
                let proj_ref = self.encode_place(Place::from(*dest));

                let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx);
                let e_rvalue_ty = self.deps.require_ref::<CapabilityEnc>(
                    rvalue_ty,
                ).unwrap();

                // The snapshot of the value that we are assigning.
                let expr = match rvalue {
                    mir::Rvalue::Use(op) => self.encode_operand_snap(op),

                    //mir::Rvalue::Repeat(Operand<'tcx>, Const<'tcx>) => {}
                    //mir::Rvalue::Ref(Region<'tcx>, BorrowKind, Place<'tcx>) => {}
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'tcx>) => {}
                    //mir::Rvalue::Len(Place<'tcx>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'tcx>, Ty<'tcx>) => {}

                    rv@mir::Rvalue::BinaryOp(op, box (l, r)) |
                    rv@mir::Rvalue::CheckedBinaryOp(op, box (l, r)) => {
                        let l_ty = l.ty(self.local_decls, self.vcx.tcx);
                        let r_ty = r.ty(self.local_decls, self.vcx.tcx);
                        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
                        let task = if matches!(rv, mir::Rvalue::BinaryOp(..)) {
                            BinOp(rvalue_ty, *op, l_ty, r_ty)
                        } else {
                            CheckedBinOp(rvalue_ty, *op, l_ty, r_ty)
                        };
                        let binop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            task
                        ).unwrap().function;
                        binop_function.apply(self.vcx, &[
                            self.encode_operand_snap(l),
                            self.encode_operand_snap(r),
                        ])
                    }

                    //mir::Rvalue::NullaryOp(NullOp, Ty<'tcx>) => {}

                    mir::Rvalue::UnaryOp(unop, operand) => {
                        let operand_ty = operand.ty(self.local_decls, self.vcx.tcx);
                        let unop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                rvalue_ty,
                                *unop,
                                operand_ty,
                            ),
                        ).unwrap().function;
                        unop_function.apply(self.vcx, &[self.encode_operand_snap(operand)])
                        /*
                        assert!(source.projection.is_empty());
                        let source_version = self.ssa_analysis.version.get(&(location, source.local)).unwrap();
                        let source_name = vir::vir_format!(self.vcx, "_{}s_{}", source.local.index(), source_version);

                        let unop_function = self.deps.require_ref::<crate::encoders::MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                *unop,
                                source.ty(self.local_decls, self.vcx.tcx).ty,
                            ),
                        ).unwrap().name;
                        Some(self.vcx.mk_func_app(
                            unop_function,
                            &[self.vcx.mk_local_ex(source_name)],
                        ))*/
                    }

                    mir::Rvalue::Aggregate(
                        box kind @ (mir::AggregateKind::Adt(..) | mir::AggregateKind::Tuple),
                        fields,
                    ) => {
                        let sl = match kind {
                            mir::AggregateKind::Adt(_, vidx, _, _, _) =>
                                e_rvalue_ty.get_variant_any(*vidx),
                            _ => e_rvalue_ty.expect_structlike()
                        };
                        let cons_args: Vec<_> = fields.iter().map(|field| self.encode_operand_snap(field)).collect();
                        sl.snap_data.field_snaps_to_snap.apply(self.vcx, &cons_args)
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx);
                        let ty = self.deps.require_ref::<CapabilityEnc>(place_ty.ty).unwrap();
                        let place_expr = self.encode_place(Place::from(*place));

                        match ty.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(el) => {
                                let discr_expr = self.vcx.mk_field_expr(place_expr, el.as_ref().unwrap().discr);
                                self.vcx.mk_unfolding_expr(ty.ref_to_pred.apply(self.vcx, [place_expr], Some(self.vcx.mk_wildcard())), discr_expr)
                            }
                            None => {
                                // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                let zero = self.vcx.mk_uint::<0>();
                                e_rvalue_ty.expect_prim().prim_to_snap.apply(self.vcx, [zero])
                            }
                        }
                    }

                    mir::Rvalue::Ref(_, kind, source) => {
                        let place_ty = source.ty(self.local_decls, self.vcx.tcx);
                        assert!(place_ty.variant_index.is_none());
                        let perm = match kind {
                            mir::BorrowKind::Shared => e_rvalue_ty.expect_ref().perm,
                            mir::BorrowKind::Shallow => todo!(),
                            mir::BorrowKind::Mut { kind: mir::MutBorrowKind::Default } => e_rvalue_ty.expect_ref().perm,
                            mir::BorrowKind::Mut { .. } => todo!(),
                        };
                        let place_expr = self.encode_place(Place::from(*source));
                        e_rvalue_ty.expect_ref().snap_data.shallow.field_snaps_to_snap.apply(self.vcx, &[place_expr])
                    }

                    //mir::Rvalue::Discriminant(Place<'tcx>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'tcx>, Ty<'tcx>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'tcx>) => {}
                    other => {
                        tracing::error!("unsupported rvalue {other:?}");
                        self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "rvalue {rvalue:?}"))
                    }
                };

                let dest_ty = dest.ty(self.local_decls, self.vcx.tcx);
                assert!(dest_ty.variant_index.is_none());
                let dest_ty_out = self.deps.require_ref::<CapabilityEnc>(dest_ty.ty,).unwrap();

                assert_eq!(dest.projection.len(), 0);
                // self.heap.insert(dest.local, expr);
                // self.stmt(self.vcx.alloc(dest_ty_out.method_assign.apply(self.vcx, &[], [proj_ref, expr])));
            }

            mir::StatementKind::StorageLive(local) => {
                // self.stmt(
                //     self.vcx.mk_new_stmt(self.local_defs[*local].pure_local_ex, Some(&[self.field.field]))
                // );
            }
            mir::StatementKind::StorageDead(local) => {
                // self.stmt(self.vcx.mk_exhale_stmt(self.local_defs[*local].local_field.unwrap()));
            }

            // no-ops
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Retag(..)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(_)
            //| mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => {}

            k => todo!("statement {k:?}"),
        }
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
        return;
        self.stmt(self.vcx.mk_comment_stmt(
            // TODO: also add bb and location for better debugging?
            vir::vir_format!(self.vcx, "{:?}", terminator.kind),
        ));

        self.fpcs_repacks_location(location, |loc| &loc.repacks_start);
        // TODO: move this to after getting operands, before assignment
        self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);
        let terminator = match &terminator.kind {
            mir::TerminatorKind::Goto { target }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .location
                        .block,
                    target
                );
                self.fpcs_repacks_terminator(REAL_TARGET_SUCC_IDX, |rep| &rep.repacks_start);

                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                //let discr_version = self.ssa_analysis.version.get(&(location, discr.local)).unwrap();
                //let discr_name = vir::vir_format!(self.vcx, "_{}s_{}", discr.local.index(), discr_version);
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx);
                let discr_ty = self
                    .deps
                    .require_ref::<CapabilityEnc>(discr_ty_rs)
                    .unwrap()
                    .expect_prim();

                let goto_targets = self.vcx.alloc_slice(
                    &targets
                        .iter()
                        .enumerate()
                        .map(|(idx, (value, target))| {
                            assert_eq!(
                                self.current_fpcs.as_ref().unwrap().terminator.succs[idx]
                                    .location
                                    .block,
                                target
                            );

                            let extra_stmts =
                                self.collect_terminator_repacks(idx, |rep| &rep.repacks_start);
                            (
                                discr_ty.expr_from_bits(discr_ty_rs, value),
                                self.vcx
                                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                                self.vcx.alloc_slice(&extra_stmts),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                let goto_otherwise = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(
                    targets.otherwise().as_usize(),
                ));

                let otherwise_succ_idx = goto_targets.len();
                assert_eq!(
                    self.current_fpcs.as_ref().unwrap().terminator.succs[otherwise_succ_idx]
                        .location
                        .block,
                    targets.otherwise()
                );
                let otherwise_stmts =
                    self.collect_terminator_repacks(otherwise_succ_idx, |rep| &rep.repacks_start);

                let discr_ex = discr_ty
                    .snap_to_prim
                    .apply(self.vcx, [self.encode_operand_snap(discr)]);
                self.vcx.mk_goto_if_stmt(
                    discr_ex, // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => self
                .vcx
                .mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::End)),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                // TODO: extracting FnDef given func could be extracted? (duplication in pure)
                let func_ty = func.ty(self.local_decls, self.vcx.tcx);
                let (func_def_id, arg_tys) = match func_ty.kind() {
                    &ty::TyKind::FnDef(def_id, arg_tys) => (def_id, arg_tys),
                    _ => todo!(),
                };
                let is_pure = crate::encoders::with_proc_spec(func_def_id, |spec| {
                    spec.kind.is_pure().unwrap_or_default()
                })
                .unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination));

                let task = (func_def_id, arg_tys, self.def_id);
                if is_pure {
                    let pure_func = self.deps.require_ref::<MirFunctionEnc>(task).unwrap();

                    let func_args: Vec<_> =
                        args.iter().map(|op| self.encode_operand_snap(op)).collect();
                    let pure_func_app = pure_func.function_ref.apply(self.vcx, &func_args);
                    let return_ty = destination.ty(self.local_decls, self.vcx.tcx).ty;
                    let method_assign = self
                        .deps
                        .require_ref::<CapabilityEnc>(return_ty)
                        .unwrap()
                        .method_assign;

                    self.stmt(self.vcx.alloc(method_assign.apply(
                        self.vcx,
                        &[],
                        [dest, pure_func_app],
                    )));
                } else {
                    let func_out = self
                        .deps
                        .require_ref::<SymImpureEnc>((task.0, task.1, Some(task.2)))
                        .unwrap();

                    let method_in = args.iter().map(|op| self.encode_operand(op));
                    let method_args: Vec<_> = method_in.collect();

                    self.stmt(self.vcx.alloc(func_out.method_ref.apply(
                        self.vcx,
                        &[dest],
                        &method_args,
                    )));
                }

                target
                    .map(|target| {
                        self.vcx.mk_goto_stmt(
                            self.vcx
                                .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                        )
                    })
                    .unwrap_or_else(|| self.unreachable())
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => {
                let e_bool = self
                    .deps
                    .require_ref::<CapabilityEnc>(self.vcx.tcx.types.bool)
                    .unwrap();
                let enc = self.encode_operand_snap(cond);
                let enc = e_bool.expect_prim().snap_to_prim.apply(self.vcx, [enc]);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self
                    .vcx
                    .mk_bin_op_expr(vir::BinOpKind::CmpEq, enc, expected);
                self.stmt(self.vcx.mk_exhale_stmt(assert));

                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                let otherwise = match unwind {
                    mir::UnwindAction::Cleanup(bb) => self
                        .vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(bb.as_usize())),
                    _ => todo!(),
                };

                self.vcx.mk_goto_if_stmt(
                    enc,
                    self.vcx.alloc_slice(&[(expected, &target_bb, &[])]),
                    otherwise,
                    &[],
                )
            }
            mir::TerminatorKind::Unreachable => self.unreachable(),

            unsupported_kind => self.vcx.mk_dummy_stmt(vir::vir_format!(
                self.vcx,
                "terminator {unsupported_kind:?}"
            )),
        };
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
