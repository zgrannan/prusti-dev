use std::{collections::hash_map::DefaultHasher, marker::PhantomData};

use pcs::combined_pcs::BodyWithBorrowckFacts;
use prusti_rustc_interface::{
    abi,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use std::hash::{Hash, Hasher};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    value::{Substs, SymValueData, SymValueKind},
    Assertion,
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
    pub fn_debug_name: String,
    pub method: vir::Method<'vir>,
}

use crate::{
    encoder_traits::pure_function_enc::mk_type_assertion,
    encoders::{
        lifted::{cast::CastToEnc, casters::CastTypePure},
        ConstEnc, MirBuiltinEnc,
    },
};

use super::{
    lifted::{
        cast::CastArgs, func_app_ty_params::LiftedFuncAppTyParamsEnc,
        func_def_ty_params::LiftedTyParamsEnc, rust_ty_cast::RustTyCastersEnc,
    },
    mir_base::MirBaseEnc,
    mir_pure::PureKind,
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym::expr::SymExprEncoder,
    sym_pure::{
        PrustiPathConditions, PrustiSemantics, PrustiSubsts, PrustiSymValSynthetic,
        PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult,
    },
    sym_spec::SymSpecEnc,
    FunctionCallTaskDescription, MirBuiltinEncTask, PureFunctionEnc, SpecEnc, SpecEncTask,
    SymFunctionEnc, SymPureEnc, SymPureEncTask,
};

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
                .body()
                .as_ref()
                .clone();

            let local_decls = body.body.local_decls.clone();
            let arg_count = body.body.arg_count;

            let arena = SymExContext::new(vcx.tcx());

            let fn_debug_name = vcx.tcx().def_path_str_with_args(def_id, substs);
            let debug_dir = std::env::var("PCS_VIS_DATA_DIR").map(|dir| {
                let mut hasher = DefaultHasher::new();
                fn_debug_name.hash(&mut hasher);
                let hash = format!("{:x}", hasher.finish());
                format!("{}/{}", dir, hash)
            });

            let symbolic_execution = symbolic_execution::run_symbolic_execution(
                &body.body.clone(),
                vcx.tcx(),
                pcs::run_free_pcs(
                    &BodyWithBorrowckFacts {
                        body: body.body,
                        promoted: body.promoted,
                        borrow_set: body.borrow_set,
                        region_inference_context: body.region_inference_context,
                        location_table: body.location_table,
                        input_facts: body.input_facts,
                        output_facts: body.output_facts,
                    },
                    vcx.tcx(),
                    debug_dir.clone().ok().as_deref(),
                ),
                PrustiSemantics(PhantomData),
                &arena,
                debug_dir.ok().as_deref(),
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
                deps.require_ref::<RustTySnapshotsEnc>(local_decls.iter().next().unwrap().ty)
                    .unwrap()
                    .generic_snapshot
                    .snapshot,
            );
            let spec = SymSpecEnc::encode(&arena, deps, (def_id, substs, caller_def_id));

            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut stmts = Vec::new();
            let mut visitor = EncVisitor {
                vcx,
                local_decls: &local_decls,
                encoder: SymExprEncoder::new(
                    vcx,
                    deps,
                    &arena,
                    symvar_locals
                        .iter()
                        .map(|local| vcx.mk_local_ex(local.name, local.ty))
                        .collect::<Vec<_>>(),
                    def_id,
                ),
                arena: &arena,
            };

            for arg in ty_arg_decls {
                stmts.push(vcx.mk_local_decl_stmt(arg.decl(), None));
            }

            for local in symvar_locals.iter() {
                stmts.push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
            }
            stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            for (local, symvar) in symvar_locals.iter().zip(symbolic_execution.symvars.iter()) {
                if let Some(expr) = mk_type_assertion(
                    vcx,
                    visitor.encoder.deps,
                    vcx.mk_local_ex(local.name, local.ty),
                    *symvar,
                ) {
                    stmts.push(vcx.mk_inhale_stmt(expr));
                }
            }

            for pre in spec.pres.into_iter() {
                match visitor.encoder.encode_pure_spec(&pre, None) {
                    Ok(pre) => {
                        stmts.push(vcx.mk_inhale_stmt(pre));
                    }
                    Err(err) => {
                        stmts.push(vcx.mk_comment_stmt(vcx.alloc(format!("Encoding err: {err}"))));
                        stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false>()));
                    }
                }
            }

            for (path, pcs, assertion) in symbolic_execution.assertions.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                match visitor.encode_pc_assertion(pcs, assertion) {
                    Ok(assertion) => {
                        stmts.extend(assertion);
                    }
                    Err(err) => {
                        stmts.push(vcx.mk_comment_stmt(vcx.alloc(format!("Encoding err: {err}"))));
                        stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false>()));
                    }
                }
            }
            for (path, pcs, expr) in symbolic_execution.paths.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));

                // Generate assertions ensuring that `expr` satisfies each
                // postcondition attached to the function definition
                let assertions: Vec<_> = spec
                    .posts
                    .iter()
                    .flat_map(|p| {
                        // The postcondition may refer to `result`; in this case
                        // `expr` should be considered as the result. The
                        // postcondition is encoded as a fn taking all arguments
                        // of this function plus an extra argument corresponding
                        // Therefore, the symbolic value at argument `body.arg_count`
                        // corresponds to the spec's symbolic input argument.
                        visitor.encoder.encode_pure_spec(
                            p,
                            Some(arena.alloc(Substs::singleton(arg_count, expr))),
                        )
                        .map(|expr| vec![vcx.mk_exhale_stmt(expr)])
                        .unwrap_or_else(|err| {
                            vec![
                            vcx.mk_comment_stmt(
                                vir_format!(vcx, "Error when encoding the postcondition {:?} of {:?} for path {:?}: {}", p, def_id, path, err)
                            ),
                            vcx.mk_exhale_stmt(vcx.mk_bool::<false>())
                            ]
                        })
                    })
                    .collect();
                match visitor.encoder.encode_path_condition(pcs) {
                    Some(Ok(pc)) => {
                        let if_stmt = vcx.mk_if_stmt(pc, vcx.alloc_slice(&assertions), &[]);
                        stmts.push(if_stmt);
                    }
                    Some(Err(err)) => {
                        stmts.push(vcx.mk_comment_stmt(vcx.alloc(format!("Encoding err: {err}"))));
                        stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false>()));
                    }
                    None => stmts.extend(assertions),
                }
            }

            Ok((
                MirImpureEncOutput {
                    fn_debug_name,
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
    encoder: SymExprEncoder<'enc, 'vir, 'sym, 'tcx, SymImpureEnc>,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    arena: &'sym SymExContext<'tcx>,
}

impl<'vir, 'enc> MirBaseEnc<'vir, 'enc> for EncVisitor<'_, 'vir, 'vir, 'enc> {
    fn get_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'vir> {
        &self.local_decls[local]
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, SymImpureEnc> {
        self.encoder.deps
    }
}

impl<'sym, 'tcx, 'vir: 'tcx, 'enc> EncVisitor<'sym, 'tcx, 'vir, 'enc> {
    fn encode_assertion(
        &mut self,
        assertion: &PrustiAssertion<'sym, 'tcx>,
    ) -> Vec<vir::Stmt<'vir>> {
        match assertion {
            Assertion::False => vec![self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>())],
            Assertion::Precondition(def_id, substs, args) => {
                let arg_substs = self
                    .arena
                    .alloc(Substs::from_iter(args.iter().copied().enumerate()));
                let encoded_pres =
                    SymSpecEnc::encode(self.arena, self.deps(), (*def_id, substs, None))
                        .pres
                        .into_iter()
                        .map(|p| self.encoder.encode_pure_spec(&p, Some(arg_substs)))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                vec![self.vcx.mk_exhale_stmt(self.vcx.mk_conj(&encoded_pres))]
            }
            Assertion::Eq(expr, val) => match self.encoder.encode_sym_value_as_prim(expr) {
                Ok(expr) => {
                    let expr = if *val {
                        self.vcx.mk_eq_expr(expr, self.vcx.mk_bool::<true>())
                    } else {
                        self.vcx.mk_eq_expr(expr, self.vcx.mk_bool::<false>())
                    };
                    vec![self.vcx.mk_exhale_stmt(expr)]
                }
                Err(err) => {
                    vec![
                        self.vcx.mk_comment_stmt(
                            self.vcx
                                .alloc(format!("Error when encoding the assertion: {err}")),
                        ),
                        self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()),
                    ]
                }
            },
        }
    }

    fn encode_pc_assertion(
        &mut self,
        pc: &PrustiPathConditions<'sym, 'tcx>,
        assertion: &PrustiAssertion<'sym, 'tcx>,
    ) -> Result<Vec<vir::Stmt<'vir>>, String> {
        if let Some(pc_expr) = self.encoder.encode_path_condition(pc) {
            let pc_expr = match pc_expr {
                Ok(expr) => expr,
                Err(err) => return Err(err),
            };
            Ok(vec![self.vcx.mk_if_stmt(
                pc_expr,
                self.vcx.alloc_slice(&self.encode_assertion(assertion)),
                &[],
            )])
        } else {
            Ok(self.encode_assertion(assertion))
        }
    }
}
