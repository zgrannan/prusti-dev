use std::{
    collections::{hash_map::DefaultHasher, BTreeMap, BTreeSet},
    marker::PhantomData,
};

use pcs::{
    borrows::domain::MaybeOldPlace, combined_pcs::BodyWithBorrowckFacts, utils::PlaceRepacker,
};
use prusti_rustc_interface::{
    abi,
    hir::Mutability,
    index::IndexVec,
    middle::{
        mir::{self, interpret::Scalar, Local, LocalDecl, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use rustc_middle::mir::RETURN_PLACE;
use std::hash::{Hash, Hasher};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    results::{ResultAssertion, ResultPath, SymbolicExecutionResult},
    value::{BackwardsFn, Substs, SymValueData, SymValueKind, SymVar},
    Assertion, SymExParams,
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, CallableIdent, DomainIdent, MethodIdent, TypeData, UnknownArity};

pub struct SymImpureEnc;

#[derive(Clone, Debug)]
pub enum MirImpureEncError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,

    /// Backwards functions for the method
    pub backwards_ref: Option<BackwardsRef<'vir>>,
}

impl<'vir> MirImpureEncOutputRef<'vir> {
    pub fn back_function_ident(&self) -> vir::FunctionIdent<'vir, UnknownArity<'vir>> {
        self.backwards_ref
            .as_ref()
            .unwrap_or_else(|| {
                panic!("No backwards function found for {:?}", self.method_ref);
            })
            .back_function_ident
    }
    pub fn composite_back_fn_app(
        &self,
        ty_args: Vec<vir::Expr<'vir>>,
        args: Vec<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        vir::with_vcx(|vcx| {
            self.back_function_ident().apply(
                vcx,
                vcx.alloc_slice(
                    &ty_args
                        .into_iter()
                        .chain(args.into_iter())
                        .collect::<Vec<_>>(),
                ),
            )
        })
    }
    pub fn backwards_expr(
        &self,
        arg: mir::Local,
        ty_args: Vec<vir::Expr<'vir>>,
        args: Vec<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        self.backwards_ref
            .as_ref()
            .unwrap()
            .apply(arg, ty_args, args)
    }
}

impl<'vir> task_encoder::OutputRefAny for MirImpureEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutput<'vir> {
    pub debug_ids: BTreeSet<String>,
    pub method: vir::Method<'vir>,
    pub backwards_domain: Option<vir::Domain<'vir>>,
    pub backwards_method: Option<vir::Method<'vir>>,
    pub backwards_fns: Vec<vir::Function<'vir>>,
}
use crate::{
    debug::{fn_debug_name, visualization_data_dir},
    encoder_traits::pure_function_enc::mk_type_assertion,
    encoders::{
        domain::DomainEnc,
        lifted::{cast::CastToEnc, casters::CastTypePure},
        most_generic_ty::extract_type_params,
        sym_spec::SymSpec,
        ConstEnc, MirBuiltinEnc,
    },
};

use self::forward_backwards_shared::ForwardBackwardsShared;

use super::{
    super::{
        lifted::{
            cast::CastArgs, func_app_ty_params::LiftedFuncAppTyParamsEnc,
            func_def_ty_params::LiftedTyParamsEnc, generic::LiftedGeneric,
            rust_ty_cast::RustTyCastersEnc,
        },
        mir_base::MirBaseEnc,
        mir_pure::PureKind,
        rust_ty_snapshots::RustTySnapshotsEnc,
        sym::{backwards::mk_backwards_method, expr::SymExprEncoder},
        sym_pure::{
            PrustiPathConditions, PrustiSemantics, PrustiSubsts, PrustiSymValSynthetic,
            PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult,
        },
        sym_spec::SymSpecEnc,
        FunctionCallTaskDescription, MirBuiltinEncTask, PureFunctionEnc, SpecEnc, SpecEncTask,
        SymFunctionEnc, SymPureEnc, SymPureEncTask,
    },
    assertion::AssertionEncoder,
    backwards::{encode_backwards_ref, mk_backwards_fn, BackwardsFnContext, BackwardsRef},
};

pub mod forward_backwards_shared;

pub type PrustiAssertion<'sym, 'tcx> = Assertion<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

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

    type EncodingError = String;

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

            let body = vcx
                .body_mut()
                .get_impure_fn_body_identity(local_def_id)
                .body()
                .as_ref()
                .clone();

            let local_decls = body.body.local_decls.clone();
            let arg_count = body.body.arg_count;

            let arena = SymExContext::new(vcx.tcx());

            let debug_dir = visualization_data_dir(def_id, substs);

            let body_with_facts = BodyWithBorrowckFacts {
                body: body.body.clone(),
                promoted: body.promoted,
                borrow_set: body.borrow_set,
                region_inference_context: body.region_inference_context,
                location_table: body.location_table,
                input_facts: body.input_facts,
                output_facts: body.output_facts,
            };

            let fpcs_analysis = pcs::run_free_pcs(&body_with_facts, vcx.tcx(), debug_dir.clone());

            let symbolic_execution = symbolic_execution::run_symbolic_execution(SymExParams {
                def_id: def_id.as_local().unwrap(),
                body: &body.body,
                tcx: vcx.tcx(),
                fpcs_analysis,
                verifier_semantics: PrustiSemantics(PhantomData),
                arena: &arena,
                debug_output_dir: debug_dir,
                new_symvars_allowed: true,
            });

            let spec = deps
                .require_local::<SymSpecEnc>((def_id, substs, caller_def_id))
                .unwrap();

            let mut debug_ids = spec.debug_ids();

            let result_local = vcx.mk_local(
                "res",
                deps.require_ref::<RustTySnapshotsEnc>(body.body.local_decls[RETURN_PLACE].ty)
                    .unwrap()
                    .generic_snapshot
                    .snapshot,
            );

            let symvar_substs = mk_symvar_substs(vcx, &body.body, &symbolic_execution, deps);

            let ty_args = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();

            let input_tys: Vec<_> = ty_args
                .iter()
                .map(|l| l.ty())
                .chain(
                    body.body
                        .args_iter()
                        .map(|local| symvar_substs[&SymVar::Input(local)].ty),
                )
                .collect();

            let backwards_ref = encode_backwards_ref(
                method_name,
                input_tys,
                &body.body,
                &symvar_substs,
                result_local,
            );

            let output_ref = MirImpureEncOutputRef {
                method_ref: method_ident,
                backwards_ref: backwards_ref.clone(),
            };
            deps.emit_output_ref(*task_key, output_ref.clone())?;

            let mut visitor = EncVisitor {
                deps,
                vcx,
                local_decls: &local_decls,
                encoder: SymExprEncoder::new(
                    vcx,
                    &arena,
                    BTreeMap::from_iter(body.body.args_iter().map(|local| {
                        (
                            local,
                            arena.mk_var(SymVar::Input(local), body.body.local_decls[local].ty),
                        )
                    })),
                    symvar_substs
                        .iter()
                        .map(|(k, v)| (*k, vcx.mk_local_ex(v.name, v.ty)))
                        .collect(),
                    def_id,
                ),
                arena: &arena,
            };

            let spec_precondition_exprs =
                encode_spec_exprs(spec.pres, &visitor.encoder, visitor.deps);

            let fb_shared = ForwardBackwardsShared::new(
                &symbolic_execution,
                substs,
                symvar_substs.clone(),
                spec_precondition_exprs,
                &body.body,
                result_local,
                ty_args,
                visitor.deps,
            );

            let mut stmts = Vec::new();

            stmts.extend(fb_shared.decl_stmts.clone());
            stmts.extend(
                fb_shared
                    .precondition_exprs
                    .iter()
                    .map(|e| vcx.mk_inhale_stmt(e)),
            );
            stmts.extend(
                fb_shared.body_type_assertion_stmts.iter()
            );

            for ResultAssertion {
                path,
                pcs,
                assertion,
            } in symbolic_execution.assertions.iter()
            {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "Assertion for path: {:?}", path)));
                match visitor.encode_pc_assertion(pcs, assertion) {
                    Ok(assertion) => {
                        stmts.extend(assertion);
                    }
                    Err(err) => {
                        stmts
                            .push(vcx.mk_comment_stmt(vcx.alloc(format!("Encoding err: {err:?}"))));
                        stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false, !, !>()));
                    }
                }
            }
            for path in symbolic_execution.paths.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path.path())));

                match path {
                    ResultPath::Return {
                        path,
                        pcs,
                        result,
                        backwards_facts: _,
                        heap,
                    } => {
                        // The postcondition may refer to `result`; in this case
                        // `expr` should be considered as the result. The
                        // postcondition is encoded as a fn taking all arguments
                        // of this function plus an extra argument corresponding
                        // Therefore, the symbolic value at argument `body.arg_count`
                        // corresponds to the spec's symbolic input argument.
                        let substs = arena.alloc(Substs::from_iter(
                            body.body
                                .args_iter()
                                .flat_map(|local| {
                                    if body.body.local_decls[local].ty.ref_mutability()
                                        == Some(Mutability::Mut)
                                    {
                                        // TODO: Should this always be gettable?
                                        heap.get(&MaybeOldPlace::Current {
                                            place: local.into(),
                                        })
                                        .map(|expr| (SymVar::Input(local), expr))
                                    } else {
                                        None
                                    }
                                })
                                .chain(std::iter::once((SymVar::nth_input(arg_count), *result))),
                        ));

                        // Generate assertions ensuring that `expr` satisfies each
                        // postcondition attached to the function definition
                        let assertions: Vec<_> = spec
                    .posts
                    .iter()
                    .flat_map(|p| {
                        visitor.encoder.encode_pure_spec(
                            visitor.deps,
                            p.clone().subst(&arena, substs),
                        )
                        .map(|spec|
                            spec.exhale_stmts(vcx)
                        )
                        .unwrap_or_else(|err| {
                            vec![
                            vcx.mk_comment_stmt(
                                vir_format!(
                                    vcx,
                                    "Error when encoding the postcondition {:?} of {:?} for path {:?}: {:?}",
                                    p, def_id, path, err
                                )
                            ),
                            vcx.mk_exhale_stmt(vcx.mk_bool::<false, !, !>())
                            ]
                        })
                    })
                    .collect();
                        let encoded_pc = visitor
                            .encoder
                            .encode_path_condition(visitor.deps, pcs)
                            .unwrap();
                        stmts.extend(encoded_pc.conditionalize_stmts(vcx, assertions));
                    }
                    ResultPath::Loop { path: _, pcs: _ } => {
                        // TODO
                    }
                }
            }

            let backwards_fns = if let Some(ref backwards_ref) = backwards_ref {
                vec![mk_backwards_fn(
                    visitor.encoder.arena,
                    &backwards_ref,
                    &spec.pledges,
                    BackwardsFnContext {
                        output_ref,
                        def_id,
                        substs,
                        caller_def_id,
                        shared: &fb_shared,
                    },
                    visitor.encoder.old_values.clone(),
                    visitor.deps,
                )]
            } else {
                vec![]
            };

            let backwards_method = mk_backwards_method(
                method_name,
                fb_shared,
                visitor.deps,
                &visitor.encoder,
                &symbolic_execution,
                &spec.pledges,
            );

            let backwards_method = match backwards_method {
                Ok(method) => Some(method),
                Err(err) => {
                    eprintln!("error encoding backwards method {err}");
                    None
                }
            };

            debug_ids.insert(fn_debug_name(def_id, substs));

            Ok((
                MirImpureEncOutput {
                    debug_ids,
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
                    backwards_method,
                    backwards_fns,
                    backwards_domain: backwards_ref.map(|b| b.domain),
                },
                (),
            ))
        })
    }
}

fn encode_spec_exprs<'sym, 'tcx, 'vir, 'deps>(
    spec: SymSpec<'sym, 'tcx>,
    encoder: &SymExprEncoder<'vir, 'sym, 'tcx>,
    deps: &'deps mut TaskEncoderDependencies<'vir, SymImpureEnc>,
) -> Vec<vir::Expr<'vir>> {
    spec.into_iter()
        .flat_map(|pre| encoder.encode_pure_spec(deps, pre).unwrap().clauses)
        .collect()
}

fn mk_symvar_substs<'sym, 'tcx, 'vir: 'tcx, 'deps>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    body: &'sym mir::Body<'tcx>,
    symex_result: &'sym SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
    deps: &'deps mut TaskEncoderDependencies<'vir, SymImpureEnc>,
) -> BTreeMap<SymVar, vir::Local<'vir>> {
    let input_symvars = body
        .args_iter()
        .map(|local| {
            let ty = body.local_decls[local].ty;
            (
                SymVar::Input(local),
                vcx.mk_local(
                    vir_format!(vcx, "i{}", local.as_usize()),
                    deps.require_ref::<RustTySnapshotsEnc>(ty)
                        .unwrap()
                        .generic_snapshot
                        .snapshot,
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let fresh_symvars = symex_result
        .fresh_symvars
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            (
                SymVar::Fresh(idx),
                vcx.mk_local(
                    vir_format!(vcx, "f{}", idx),
                    deps.require_ref::<RustTySnapshotsEnc>(*ty)
                        .unwrap()
                        .generic_snapshot
                        .snapshot,
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    input_symvars
        .into_iter()
        .chain(fresh_symvars.into_iter())
        .collect::<BTreeMap<_, _>>()
}

struct EncVisitor<'sym, 'tcx, 'vir, 'enc>
where
    'vir: 'enc,
{
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir, SymImpureEnc>,
    encoder: SymExprEncoder<'vir, 'sym, 'tcx>,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    arena: &'sym SymExContext<'tcx>,
}

impl<'vir, 'enc> MirBaseEnc<'vir, 'enc> for EncVisitor<'_, 'vir, 'vir, 'enc> {
    fn get_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'vir> {
        &self.local_decls[local]
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, SymImpureEnc> {
        self.deps
    }
}

impl<'slf, 'sym, 'tcx, 'vir: 'tcx, 'enc> EncVisitor<'sym, 'tcx, 'vir, 'enc> {
    fn encode_pc_assertion(
        &mut self,
        pc: &PrustiPathConditions<'sym, 'tcx>,
        assertion: &PrustiAssertion<'sym, 'tcx>,
    ) -> Result<Vec<vir::Stmt<'vir>>, EncodeFullError<'vir, SymImpureEnc>> {
        let encoded_pc = match self.encoder.encode_path_condition(self.deps, pc) {
            Ok(pc) => pc,
            Err(err) => {
                panic!("Error when encoding path condition {:?}: {:?}", pc, err);
                // return Ok(vec![
                //     self.vcx.mk_comment_stmt(
                //         self.vcx
                //             .alloc(format!("Error when encoding path condition: {:?}", err)),
                //     ),
                //     self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false, !, !>()),
                // ])
            }
        };
        let assertion_encoder = AssertionEncoder::new(self.vcx, &self.encoder);
        let encoded_assertion = assertion_encoder.encode_assertion(self.deps, assertion);
        Ok(encoded_pc.conditionalize_stmts(self.vcx, encoded_assertion))
    }
}
