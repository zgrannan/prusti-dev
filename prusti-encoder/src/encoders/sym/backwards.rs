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
        mir::{self, interpret::Scalar, Local, LocalDecl, ProjectionElem},
        ty::{self, GenericArgsRef},
    },
    span::def_id::{DefId, LocalDefId},
};

use super::{expr::SymExprEncoder, impure::MirImpureEncOutputRef};

pub struct BackwardsFnContext<'shared, 'vir, 'tcx> {
    pub output_ref: MirImpureEncOutputRef<'vir>,
    pub def_id: DefId,
    pub substs: GenericArgsRef<'tcx>,
    pub caller_def_id: Option<DefId>,
    pub shared: &'shared ForwardBackwardsShared<'vir, 'tcx>,
}

pub fn mk_backwards_fn_axioms<
    'shared,
    'vir,
    'sym,
    'tcx,
    'enc,
    T: TaskEncoder<EncodingError = String>,
>(
    pledges: &SymSpec<'sym, 'tcx>,
    ctxt: BackwardsFnContext<'shared, 'vir, 'tcx>,
    encoder: &SymExprEncoder<'vir, 'sym, 'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir, T>,
) -> &'vir [DomainAxiom<'vir>] {
    vir::with_vcx(|vcx| {
        let back_return_snapshot =
            encoder
                .arena
                .mk_synthetic(encoder.arena.alloc(PrustiSymValSyntheticData::VirLocal(
                    ctxt.shared.result_local.name,
                    ctxt.shared.result_ty,
                )));

        let arg_snapshots = encoder.arena.alloc_slice(
            &(0..ctxt.shared.arg_count)
                .map(|i| {
                    encoder
                        .arena
                        .mk_var(SymVar::nth_input(i), ctxt.shared.nth_input_ty(i))
                })
                .collect::<Vec<_>>(),
        );

        let backward_axiom_qvars = vcx.alloc_slice(
            &ctxt
                .shared
                .ty_args
                .iter()
                .map(|l| l.decl())
                .chain(
                    ctxt.shared
                        .arg_locals()
                        .into_iter()
                        .chain(std::iter::once(ctxt.shared.result_local))
                        .map(|l| vcx.mk_local_decl(l.name, l.ty)),
                )
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
                        SymVar::nth_input(i),
                        encoder.arena.mk_backwards_fn(BackwardsFn {
                            def_id: ctxt.def_id,
                            substs: ctxt.substs,
                            caller_def_id: ctxt.caller_def_id,
                            arg_snapshots,
                            return_snapshot: back_return_snapshot,
                            arg_index: i,
                        }),
                    )
                })
                .chain(std::iter::once((
                    SymVar::nth_input(ctxt.shared.arg_count),
                    back_return_snapshot,
                ))),
        );

        let backward_fn_calls = ctxt
            .output_ref
            .backwards_fns
            .iter()
            .map(|(_, f)| f.0.apply(vcx, backward_axiom_args))
            .collect::<Vec<_>>();

        let pledge_axioms = pledges
            .iter()
            .enumerate()
            .map(|(i, pledge)| {
                let pledge = pledge.clone().subst(&encoder.arena, &pledge_axiom_substs);
                vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(
                        vcx,
                        "pledge_{}_{}_axiom",
                        ctxt.output_ref.method_ref.name(),
                        i
                    ),
                    vcx.mk_forall_expr(
                        backward_axiom_qvars,
                        vcx.alloc_slice(
                            &backward_fn_calls
                                .iter()
                                .map(|call| vcx.mk_trigger(vcx.alloc_slice(&[call])))
                                .collect::<Vec<_>>(),
                        ), // TODO, maybe too imprecise?
                        encoder.encode_pure_spec(deps, pledge).unwrap().to_expr(vcx),
                    ),
                )
            })
            .collect::<Vec<_>>();

        let ty_axioms = ctxt
            .output_ref
            .backwards_fns
            .iter()
            .map(|(i, f)| {
                let call = f.0.apply(vcx, backward_axiom_args);
                let typeof_function_arg = deps
                    .require_ref::<DomainEnc>(
                        extract_type_params(
                            vcx.tcx(),
                            ctxt.shared.symvars[&SymVar::nth_input(*i)].0,
                        )
                        .0,
                    )
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
                            typeof_function_arg
                                .apply(vcx, [backward_axiom_args[*i + ctxt.shared.ty_args.len()]]), // Skip the type arguments
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
    fb_shared: ForwardBackwardsShared<'vir, 'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir, T>,
    encoder: &SymExprEncoder<'vir, 'sym, 'tcx>,
    sym_ex_results: &SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
    pledges: &SymSpec<'sym, 'tcx>,
) -> Result<vir::Method<'vir>, String> {
    vir::with_vcx(|vcx| {
        // The map from an index in `BackwardsFact` to the backwards result local
        let back_result_vars: BTreeMap<usize, vir::Local<'vir>> = (0..fb_shared.arg_count)
            .map(|idx| {
                let name = vir::vir_format!(vcx, "backwards_{}", idx);
                let ty = fb_shared.symvars[&SymVar::nth_input(idx)].1.ty;
                (idx, vcx.mk_local(name, ty))
            })
            .collect();

        let get_back_result = |idx| {
            let local = back_result_vars.get(&idx).unwrap();
            vcx.mk_local_ex(local.name, local.ty)
        };

        let mut body_stmts = vec![];

        let result_local =
            encoder
                .arena
                .mk_synthetic(encoder.arena.alloc(PrustiSymValSyntheticData::VirLocal(
                    fb_shared.result_local.name,
                    fb_shared.result_ty,
                )));

        let pledge_substs = Substs::from_iter(
            back_result_vars
                .iter()
                .map(|(idx, local)| {
                    let symvar = SymVar::nth_input(*idx);
                    (
                        symvar,
                        encoder.arena.mk_synthetic(encoder.arena.alloc(
                            PrustiSymValSyntheticData::VirLocal(
                                local.name,
                                fb_shared.symvar_ty(symvar),
                            ),
                        )),
                    )
                })
                .chain(std::iter::once((
                    SymVar::nth_input(fb_shared.arg_count),
                    result_local,
                )))
                .collect::<Vec<_>>()
                .into_iter(),
        );

        let backwards_substs = Substs::singleton(
            SymVar::ReservedBackwardsFnResult,
            encoder
                .arena
                .mk_projection(ProjectionElem::Deref, result_local),
        );

        for path in sym_ex_results.paths.iter() {
            let mut path_stmts = vec![];
            if let Some(backwards_facts) = path.backwards_facts() {
                for (idx, expr) in backwards_facts.0.iter() {
                    let expr = expr.subst(encoder.arena, &backwards_substs);
                    let expr = encoder.arena.mk_ref(expr, Mutability::Mut);
                    let expr = encoder.encode_sym_value(deps, expr, false)?;
                    let back_local = get_back_result(*idx);
                    path_stmts.push(vcx.mk_inhale_stmt(vcx.mk_eq_expr(back_local, expr)));
                }
                for pledge in pledges.iter() {
                    let pledge = pledge.clone().subst(&encoder.arena, &pledge_substs);
                    for stmt in encoder
                        .encode_pure_spec(deps, pledge)
                        .unwrap()
                        .exhale_stmts(vcx)
                    {
                        path_stmts.push(stmt);
                    }
                }
                match encoder.encode_path_condition(deps, &path.pcs()) {
                    Some(Err(err)) => {
                        body_stmts.push(vcx.mk_comment_stmt(vir::vir_format!(
                            vcx,
                            "Error: {}",
                            err
                        )));
                        body_stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false, !, !>()));
                    }
                    Some(Ok(condition)) => {
                        body_stmts.push(vcx.mk_if_stmt(
                            condition.to_expr(vcx),
                            vcx.alloc_slice(&path_stmts),
                            &[],
                        ));
                    }
                    None => {
                        body_stmts.extend(path_stmts);
                    }
                }
            }
        }
        let method_name = vir::vir_format_identifier!(vcx, "{}_backwards", base_method_name);
        let method_ident = vir::MethodIdent::new(method_name, UnknownArity::new(&[]));
        let mut stmts = fb_shared.decl_stmts;
        for (_, local) in back_result_vars.iter() {
            stmts.push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
        }
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
        Ok(method)
    })
}
