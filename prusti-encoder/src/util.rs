use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};

pub fn to_placeholder<'tcx>(tcx: ty::TyCtxt<'tcx>, idx: Option<usize>) -> ty::Ty<'tcx> {
    let name = idx.map(|idx| format!("T{idx}")).unwrap_or_else(|| String::from("T"));
    tcx.mk_ty_from_kind(TyKind::Param(ty::ParamTy {
        index: idx.unwrap_or_default() as u32,
        name: symbol::Symbol::intern(&name),
    }))
}