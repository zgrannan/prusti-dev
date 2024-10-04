use std::collections::BTreeMap;
use symbolic_execution::{
    context::SymExContext,
    results::SymbolicExecutionResult,
    value::{BackwardsFn, Substs, SymVar},
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{
    Arity, CallableIdent, DomainAxiom, Function, Method, UnaryArity, UnknownArity, ViperIdent,
};

use crate::encoders::{
    domain::DomainEnc,
    most_generic_ty::extract_type_params,
    sym::impure::forward_backwards_shared::ForwardBackwardsShared,
    sym_pure::{PrustiSymValSynthetic, PrustiSymValSyntheticData, PrustiSymValue},
    sym_spec::SymSpec,
};
use prusti_rustc_interface::{
    abi,
    hir::Mutability,
    index::IndexVec,
    middle::{
        mir::{self, interpret::Scalar, Body, Local, LocalDecl, ProjectionElem},
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

impl<'shared, 'vir, 'tcx> BackwardsFnContext<'shared, 'vir, 'tcx> {
    pub fn nth_input_ty(&self, i: usize) -> ty::Ty<'tcx> {
        self.shared.nth_input_ty(i)
    }
}

/**
 *  Encodes the composite backwards Viper function. Note that this does not
 *  check the correctness of the pledges. (See `mk_backwards_method` for that.)
 */
pub fn mk_backwards_fn<
    'shared,
    'vir: 'tcx,
    'sym,
    'tcx: 'vir,
    'enc,
    T: TaskEncoder<EncodingError = String>,
>(
    arena: &'sym SymExContext<'tcx>,
    backwards_ref: &BackwardsRef<'vir>,
    pledges: &SymSpec<'sym, 'tcx>,
    ctxt: BackwardsFnContext<'shared, 'vir, 'tcx>,
    _old_values: BTreeMap<mir::Local, PrustiSymValue<'sym, 'tcx>>,
    deps: &'enc mut TaskEncoderDependencies<'vir, T>,
) -> Function<'vir> {
    vir::with_vcx(|vcx| {
        let arg_ty_decls = ctxt
            .shared
            .ty_args
            .iter()
            .map(|l| l.decl())
            .collect::<Vec<_>>();

        let arg_decls = ctxt
            .shared
            .arg_locals()
            .into_iter()
            .chain(std::iter::once(ctxt.shared.result_local))
            .map(|l| vcx.mk_local_decl(l.name, l.ty))
            .collect::<Vec<_>>();

        let backward_fn_decls = vcx.alloc_slice(
            &arg_ty_decls
                .into_iter()
                .chain(arg_decls.into_iter())
                .collect::<Vec<_>>(),
        );

        let composite_back_fn_ident = ctxt.output_ref.back_function_ident();

        let old_values = BTreeMap::from_iter((0..ctxt.shared.arg_count).map(|i| {
            (
                mir::Local::from_usize(i + 1),
                arena.mk_var(SymVar::Fresh(i), ctxt.nth_input_ty(i)),
            )
        }));

        let encoder = SymExprEncoder::new(
            vcx,
            arena,
            old_values,
            BTreeMap::from_iter(
                (0..ctxt.shared.arg_count)
                    .flat_map(|i| {
                        let old_value = (SymVar::Fresh(i), ctxt.shared.nth_input_expr(i));
                        let post_value = if ctxt.shared.nth_input_ty(i).ref_mutability()
                            == Some(Mutability::Mut)
                        {
                            (
                                SymVar::nth_input(i),
                                backwards_ref
                                    .accessor_ref(mir::Local::from_usize(i + 1))
                                    .ident()
                                    .apply(vcx, [vcx.mk_result(backwards_ref.domain_type())]),
                            )
                        } else {
                            (SymVar::nth_input(i), ctxt.shared.nth_input_expr(i))
                        };
                        vec![old_value, post_value]
                    })
                    .chain(std::iter::once((
                        SymVar::nth_input(ctxt.shared.arg_count),
                        vcx.mk_local_ex_local(ctxt.shared.result_local),
                    ))),
            ),
            ctxt.def_id,
        );

        vcx.mk_function(
            composite_back_fn_ident.name_str(),
            backward_fn_decls,
            composite_back_fn_ident.result_ty(),
            ctxt.shared.precondition_exprs,
            vcx.alloc_slice(
                &pledges
                    .iter()
                    .flat_map(|pledge| {
                        encoder
                            .encode_pure_spec(deps, pledge.clone())
                            .unwrap()
                            .clauses
                    })
                    .collect::<Vec<_>>(),
            ),
            None,
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
            .flat_map(|idx| {
                if fb_shared.symvar_ty(SymVar::nth_input(idx)).ref_mutability()
                    == Some(Mutability::Mut)
                {
                    let name = vir::vir_format!(vcx, "backwards_{}", idx);
                    let ty = fb_shared.symvar_vir_ty(SymVar::nth_input(idx));
                    Some((idx, vcx.mk_local(name, ty)))
                } else {
                    None
                }
            })
            .collect();

        let get_back_result = |idx| {
            if let Some(local) = back_result_vars.get(&idx) {
                vcx.mk_local_ex(local.name, local.ty)
            } else {
                fb_shared.nth_input_expr(idx)
            }
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
                    Err(err) => {
                        body_stmts.push(vcx.mk_comment_stmt(vir::vir_format!(
                            vcx,
                            "Error: {}",
                            err
                        )));
                        body_stmts.push(vcx.mk_exhale_stmt(vcx.mk_bool::<false, !, !>()));
                    }
                    Ok(condition) => {
                        body_stmts.extend(condition.conditionalize_stmts(vcx, path_stmts));
                    }
                }
            }
        }
        let method_name = vir::vir_format_identifier!(vcx, "{}_backwards", base_method_name);
        let method_ident = vir::MethodIdent::new(method_name, UnknownArity::new(&[]));
        let mut stmts = fb_shared.decl_stmts.clone();
        for (_, local) in back_result_vars.iter() {
            stmts.push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
        }
        stmts.extend(fb_shared.precondition_stmts());
        stmts.extend(fb_shared.body_type_assertion_stmts);
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

#[derive(Copy, Clone, Debug)]
/// A reference to a backwards function that returns the value of an input
/// reference after the lifetime of the function result has ended
pub struct BackwardsAccessorRef<'vir> {
    // The accessor for the resulting value of the input to f. For example,
    // for a call `r = f(x, y)`, the backwards result for `x` is e.g.
    // `get_x(f_back(x, y, r'))` where r' is the value of `r` just before it expires.
    // In the above examople `get_x` is the accessor.
    accessor: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> BackwardsAccessorRef<'vir> {
    pub fn ident(&self) -> vir::FunctionIdent<'vir, UnaryArity<'vir>> {
        self.accessor
    }
    pub fn apply(
        &self,
        back_function_ident: vir::FunctionIdent<'vir, UnknownArity<'vir>>,
        ty_args: Vec<vir::Expr<'vir>>,
        args: Vec<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        vir::with_vcx(|vcx| {
            let args = vcx.alloc_slice(
                &ty_args
                    .into_iter()
                    .chain(args.into_iter())
                    .collect::<Vec<_>>(),
            );
            self.accessor
                .apply(vcx, [back_function_ident.apply(vcx, args)])
        })
    }
}

#[derive(Clone, Debug)]
pub struct BackwardsRef<'vir> {
    /// The function that results a value of the uninterpreted "backwards" domain
    /// e.g if `f` is the function this function is `f_back`
    /// It takes as inputs all inputs to `f`, followed by the value of the result
    /// of `f` just before it expires
    pub back_function_ident: vir::FunctionIdent<'vir, UnknownArity<'vir>>,

    // Returns the domain corresponding to the (aggregate) of all backwards
    // results for a fn
    pub domain: vir::Domain<'vir>,

    // Accessors to the individual backwards results
    pub accessors: BTreeMap<Local, BackwardsAccessorRef<'vir>>,
}

impl<'vir> BackwardsRef<'vir> {
    pub fn accessor_ref(&self, arg: mir::Local) -> BackwardsAccessorRef<'vir> {
        self.accessors[&arg]
    }

    pub fn apply(
        &self,
        arg: mir::Local,
        ty_args: Vec<vir::Expr<'vir>>,
        args: Vec<vir::Expr<'vir>>,
    ) -> vir::Expr<'vir> {
        self.accessors[&arg].apply(self.back_function_ident, ty_args, args)
    }

    pub fn domain_type(&self) -> vir::Type<'vir> {
        vir::with_vcx(|vcx| vcx.alloc(vir::TypeData::Domain(self.domain.name, &[])))
    }
}

pub fn encode_backwards_ref<'tcx, 'vir>(
    method_name: ViperIdent<'vir>,
    input_tys: Vec<vir::Type<'vir>>,
    body: &Body<'tcx>,
    symvar_substs: &BTreeMap<SymVar, vir::Local<'vir>>,
    result_local: vir::Local<'vir>,
) -> Option<BackwardsRef<'vir>> {
    let backwards_fn_args = body
        .args_iter()
        .flat_map(|local| {
            let ty = body.local_decls[local].ty;
            if ty.ref_mutability() == Some(Mutability::Mut) {
                Some(local)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    if backwards_fn_args.is_empty() {
        return None;
    }
    vir::with_vcx(|vcx| {
        let back_domain_name = vir::vir_format_identifier!(vcx, "Backwards_{}", method_name);
        let back_domain_ty = vcx.alloc(vir::TypeData::Domain(back_domain_name.to_str(), &[]));
        let back_function_ident = vir::FunctionIdent::new(
            vir::vir_format_identifier!(vcx, "back_{}", method_name),
            UnknownArity::new(
                vcx.alloc_slice(
                    &input_tys
                        .into_iter()
                        .chain(std::iter::once(result_local.ty))
                        .collect::<Vec<_>>(),
                ),
            ),
            back_domain_ty,
        );

        let accessors: BTreeMap<_, _> = backwards_fn_args
            .iter()
            .map(|local| {
                let accessor = vir::FunctionIdent::new(
                    vir::vir_format_identifier!(
                        vcx,
                        "back_{}_{}",
                        method_name,
                        local.as_usize() - 1
                    ),
                    UnaryArity::new(vcx.alloc([back_domain_ty])),
                    symvar_substs[&SymVar::Input(*local)].ty,
                );
                (*local, BackwardsAccessorRef { accessor })
            })
            .collect();

        let backwards_domain = vcx.mk_domain(
            back_domain_name,
            &[],
            &[],
            vcx.alloc_slice(
                &accessors
                    .values()
                    .map(|accessor| vcx.mk_domain_function(accessor.ident(), false))
                    .collect::<Vec<_>>(),
            ),
        );
        Some(BackwardsRef {
            back_function_ident,
            domain: backwards_domain,
            accessors,
        })
    })
}
