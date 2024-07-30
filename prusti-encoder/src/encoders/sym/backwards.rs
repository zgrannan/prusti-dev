use std::collections::BTreeMap;
use symbolic_execution::{
    results::SymbolicExecutionResult,
    value::{BackwardsFn, Substs, SymVar},
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, DomainAxiom, Method, UnknownArity, ViperIdent};

use crate::encoders::{
    domain::DomainEnc,
    most_generic_ty::extract_type_params,
    sym::impure::forward_backwards_shared::ForwardBackwardsShared,
    sym_pure::{PrustiSymValSynthetic, PrustiSymValSyntheticData},
    sym_spec::SymSpec,
};
use prusti_rustc_interface::{
    abi,
    hir::Mutability,
    index::IndexVec,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, Local, LocalDecl, ProjectionElem},
        ty::{self, GenericArgsRef},
    },
    span::def_id::{DefId, LocalDefId},
};

use super::{expr::SymExprEncoder, impure::MirImpureEncOutputRef};

pub struct BackwardsFnContext<'shared, 'vir, 'sym, 'tcx> {
    pub output_ref: MirImpureEncOutputRef<'vir>,
    pub def_id: DefId,
    pub substs: GenericArgsRef<'tcx>,
    pub caller_def_id: Option<DefId>,
    pub symvars: &'sym [ty::Ty<'tcx>],
    pub shared: &'shared ForwardBackwardsShared<'vir>,
    pub result_ty: ty::Ty<'tcx>,
}

pub fn mk_backwards_fn_axioms<
    'shared,
    'vir,
    'sym,
    'tcx,
    'enc,
    T: TaskEncoder<EncodingError = String>,
>(
    pledges: SymSpec<'sym, 'tcx>,
    ctxt: BackwardsFnContext<'shared, 'vir, 'sym, 'tcx>,
    encoder: &SymExprEncoder<'vir, 'sym, 'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir, T>,
) -> &'vir [DomainAxiom<'vir>] {
    vir::with_vcx(|vcx| {
        let back_return_snapshot =
            encoder
                .arena
                .mk_synthetic(encoder.arena.alloc(PrustiSymValSyntheticData::VirLocal(
                    ctxt.shared.result_local.name,
                    ctxt.result_ty,
                )));

        let arg_snapshots = encoder.arena.alloc_slice(
            &(0..ctxt.shared.arg_count)
                .map(|i| encoder.arena.mk_var(SymVar::Normal(i), ctxt.symvars[i]))
                .collect::<Vec<_>>(),
        );

        let backward_axiom_qvars = vcx.alloc_slice(
            &ctxt
                .shared
                .arg_locals()
                .into_iter()
                .copied()
                .chain(std::iter::once(ctxt.shared.result_local))
                .map(|l| vcx.mk_local_decl(l.name, l.ty))
                .collect::<Vec<_>>(),
        );

        let backward_axiom_args = vcx.alloc_slice(
            &backward_axiom_qvars
                .iter()
                .map(|qvar| vcx.mk_local_ex(qvar.name, qvar.ty))
                .collect::<Vec<_>>(),
        );

        let pledge_axiom_substs = Substs::from_iter(
            (0..ctxt.shared.arg_count)
                .map(|i| {
                    (
                        i,
                        encoder.arena.mk_backwards_fn(BackwardsFn {
                            def_id: ctxt.def_id,
                            substs: ctxt.substs,
                            caller_def_id: ctxt.caller_def_id,
                            arg_snapshots: arg_snapshots,
                            return_snapshot: back_return_snapshot,
                            arg_index: i,
                        }),
                    )
                })
                .chain(std::iter::once((
                    ctxt.shared.arg_count,
                    back_return_snapshot,
                ))),
        );

        let backward_fn_calls = ctxt
            .output_ref
            .backwards_fns
            .iter()
            .map(|(i, f)| f.apply(vcx, backward_axiom_args))
            .collect::<Vec<_>>();

        let pledge_axioms = pledges
            .into_iter()
            .enumerate()
            .map(|(i, pledge)| {
                let pledge = pledge.subst(encoder.arena, vcx.tcx(), &pledge_axiom_substs);
                vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(
                        vcx,
                        "pledge_{}_{}_axiom",
                        ctxt.output_ref.method_ref.name(),
                        i
                    ),
                    vcx.mk_forall_expr(
                        backward_axiom_qvars,
                        vcx.alloc_slice(&backward_fn_calls
                            .iter()
                            .map(|call| vcx.mk_trigger(vcx.alloc_slice(&[call])))
                            .collect::<Vec<_>>()), // TODO, maybe too imprecise?
                        encoder.encode_pure_spec(deps, pledge, None).unwrap(),
                    ),
                )
            })
            .collect::<Vec<_>>();

        let ty_axioms = ctxt
            .output_ref
            .backwards_fns
            .iter()
            .map(|(i, f)| {
                let call = f.apply(vcx, backward_axiom_args);
                let typeof_function_arg = deps
                    .require_ref::<DomainEnc>(extract_type_params(vcx.tcx(), ctxt.symvars[*i]).0)
                    .unwrap()
                    .typeof_function;
                vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(
                        vcx,
                        "backwards_{}_{}_axiom",
                        ctxt.output_ref.method_ref.name(),
                        i
                    ),
                    vcx.mk_forall_expr(
                        backward_axiom_qvars,
                        vcx.alloc_slice(&[vcx.mk_trigger(vcx.alloc_slice(&[call]))]),
                        vcx.mk_eq_expr(
                            typeof_function_arg.apply(vcx, [backward_axiom_args[*i]]),
                            typeof_function_arg.apply(vcx, [call]),
                        ),
                    ),
                )
            })
            .collect::<Vec<_>>();
        vcx.alloc_slice(
            &pledge_axioms
                .into_iter()
                .chain(ty_axioms)
                .collect::<Vec<_>>(),
        )
    })
}

pub fn mk_backwards_method<'enc, 'vir, 'sym, 'tcx, T: TaskEncoder<EncodingError = String>>(
    base_method_name: ViperIdent<'vir>,
    mut fb_shared: ForwardBackwardsShared<'vir>,
    deps: &'enc mut TaskEncoderDependencies<'vir, T>,
    encoder: &SymExprEncoder<'vir, 'sym, 'tcx>,
    sym_ex_results: &SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
) -> vir::Method<'vir> {
    vir::with_vcx(|vcx| {
        // The map from an index in `BackwardsFact` to the backwards result local
        let mut back_result_vars: BTreeMap<usize, vir::Expr<'vir>> = BTreeMap::default();

        // Get the local for the back result for a given index in `BackwardsFact`
        let mut get_back_result = |idx| {
            if !back_result_vars.contains_key(&idx) {
                let name = vir::vir_format!(vcx, "backwards_{}", idx);
                let ty = fb_shared.symvar_locals[idx].ty;
                fb_shared
                    .decl_stmts
                    .push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(name, ty), None));
                back_result_vars.insert(idx, vcx.mk_local_ex(name, ty));
            }
            back_result_vars.get(&idx).unwrap().clone()
        };

        let mut body_stmts = vec![];
        for path in sym_ex_results.paths.iter() {
            let mut path_stmts = vec![];
            for (idx, expr) in path.backwards_facts.0.iter() {
                let expr = encoder.encode_sym_value(deps, expr).unwrap();
                let result_local = get_back_result(*idx);
                path_stmts.push(vcx.mk_inhale_stmt(vcx.mk_eq_expr(result_local, expr)));
            }
            match encoder.encode_path_condition(deps, &path.pcs) {
                Some(Err(err)) => {
                    body_stmts.push(vcx.mk_comment_stmt(vir::vir_format!(vcx, "Error: {}", err)));
                    body_stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false>()));
                }
                Some(Ok(condition)) => {
                    body_stmts.push(vcx.mk_if_stmt(condition, vcx.alloc_slice(&path_stmts), &[]));
                }
                None => {
                    body_stmts.extend(path_stmts);
                }
            }
        }
        let method_name = vir::vir_format_identifier!(vcx, "{}_backwards", base_method_name);
        let method_ident = vir::MethodIdent::new(method_name, UnknownArity::new(&[]));
        let mut stmts = fb_shared.decl_stmts;
        stmts.extend(fb_shared.type_assertion_stmts);
        stmts.extend(body_stmts);
        let method = vcx.mk_method(
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
        );
        method
    })
}
