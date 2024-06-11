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

use crate::{encoder_traits::pure_function_enc::mk_type_assertion, encoders::{
    lifted::{cast::CastToEnc, casters::CastTypePure},
    ConstEnc, MirBuiltinEnc,
}};

use super::{
    lifted::{
        cast::CastArgs, func_app_ty_params::LiftedFuncAppTyParamsEnc,
        rust_ty_cast::RustTyCastersEnc,
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
                local_decls: &body.local_decls,
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

            let mut stmts = Vec::new();

            for local in symvar_locals.iter() {
                stmts.push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
            }
            stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            for (local, symvar) in symvar_locals.iter().zip(symbolic_execution.symvars.iter()) {
                if let Some(expr) = mk_type_assertion(vcx, visitor.encoder.deps, vcx.mk_local_ex(local.name, local.ty), *symvar) {
                    stmts.push(vcx.mk_inhale_stmt(expr));
                }
            }

            for pre in spec.pres.into_iter() {
                let pre = visitor.encoder.encode_pure_spec(&pre, None).unwrap();
                stmts.push(vcx.mk_inhale_stmt(pre));
            }

            for (path, pcs, assertion) in symbolic_execution.assertions.iter() {
                stmts.push(vcx.mk_comment_stmt(vir_format!(vcx, "path: {:?}", path)));
                stmts.push(visitor.encode_pc_assertion(pcs, assertion));
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
                        visitor.encoder.encode_pure_spec(
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
                        visitor.encoder.encode_path_condition(pcs).unwrap().unwrap(),
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
    encoder: SymExprEncoder<'enc, 'vir, 'sym, 'tcx, SymImpureEnc>,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    arena: &'sym SymExArena,
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
    fn encode_assertion(&mut self, assertion: &PrustiAssertion<'sym, 'tcx>) -> vir::Stmt<'vir> {
        let expr = match assertion {
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
                self.vcx.mk_conj(&encoded_pres)
            }
            Assertion::Eq(expr, val) => {
                let expr = self.encoder.encode_sym_value_as_prim(expr);
                if *val {
                    self.vcx.mk_eq_expr(expr, self.vcx.mk_bool::<true>())
                } else {
                    self.vcx.mk_eq_expr(expr, self.vcx.mk_bool::<false>())
                }
            }
        };
        self.vcx.mk_exhale_stmt(expr)
    }

    fn encode_pc_assertion(
        &mut self,
        pc: &PrustiPathConditions<'sym, 'tcx>,
        assertion: &PrustiAssertion<'sym, 'tcx>,
    ) -> vir::Stmt<'vir> {
        if let Some(pc_expr) = self.encoder.encode_path_condition(pc) {
            self.vcx.mk_if_stmt(
                pc_expr.unwrap(),
                self.vcx.alloc_slice(&[self.encode_assertion(assertion)]),
                &[],
            )
        } else {
            self.encode_assertion(assertion)
        }
    }
}
