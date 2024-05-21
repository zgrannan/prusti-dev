use std::collections::HashSet;

use prusti_rustc_interface::middle::ty::{GenericArgs, ParamTy, Ty, TyKind};

/// Extracts all unique `ParamTy`s from the provided `GenericArgs` in the order
/// they appear. For example, if the input was `[Option<T, U>, T]`, the output
/// would be `[T, U]`.
pub fn get_unique_param_tys_in_order<'tcx>(
    generic_args: &'tcx GenericArgs<'tcx>,
) -> impl Iterator<Item = ParamTy> + 'tcx {
    unique(
        generic_args
            .iter()
            .filter_map(|arg| arg.as_type())
            .flat_map(extract_ty_params),
    )
}

fn extract_ty_params(ty: Ty<'_>) -> Vec<ParamTy> {
    match ty.kind() {
        TyKind::Param(p) => vec![*p],
        TyKind::Adt(_, args) => args
            .iter()
            .filter_map(|arg| arg.as_type())
            .flat_map(|arg| extract_ty_params(arg))
            .collect(),
        TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Bool
        | TyKind::Char
        | TyKind::Str => vec![],
        // TODO: special case to support constant strings
        _ if matches!(ty.peel_refs().kind(), TyKind::Str) => vec![],
        other => todo!("{:?}", other),
    }
}

fn unique(iter: impl IntoIterator<Item = ParamTy>) -> impl Iterator<Item = ParamTy> {
    let mut seen = HashSet::new();
    iter.into_iter().filter(move |item| seen.insert(*item))
}
