use vir::{FunctionIdent, MethodIdent, PredicateIdent, TypeData, UnknownArity, VirCtxt};

pub fn mk_method_assign<'vir, 'tcx>(
    vcx: &'vir VirCtxt<'tcx>,
    ident: MethodIdent<'vir, UnknownArity<'vir>>,
    generics: Vec<vir::LocalDecl<'vir>>,
    snapshot: vir::Type<'vir>,
    ref_to_pred: PredicateIdent<'vir, UnknownArity<'vir>>,
    ref_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
) -> vir::Method<'vir> {
    let self_local = vcx.mk_local_decl("self", &TypeData::Ref);
    let self_new_local = vcx.mk_local_decl("self_new", snapshot);

    let ref_to_args = std::iter::once(&self_local)
        .chain(generics.iter())
        .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
        .collect::<Vec<_>>();

    let self_pred_app = vcx.mk_predicate_app_expr(ref_to_pred.apply(vcx, &ref_to_args, None));

    let mut assign_args = vec![self_local];
    assign_args.extend(generics);
    assign_args.push(self_new_local);
    let assign_args = vcx.alloc_slice(&assign_args);

    let posts = vcx.alloc_slice(&[
        self_pred_app,
        vcx.mk_eq_expr(
            ref_to_snap.apply(vcx, &ref_to_args),
            vcx.mk_local_ex(self_new_local.name, snapshot),
        ),
    ]);
    vcx.mk_method(ident, &assign_args, &[], &[], posts, None)
}
