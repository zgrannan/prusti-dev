use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MostGenericTy<'tcx>(ty::Ty<'tcx>);

impl<'tcx> MostGenericTy<'tcx> {
    pub fn kind(&self) -> &TyKind<'tcx> {
        self.0.kind()
    }

    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.0
    }

    pub fn generics(&self) -> Vec<ty::Ty<'tcx>> {
        match *self.kind() {
            TyKind::Adt(_, args) => args.into_iter().flat_map(ty::GenericArg::as_type).collect(),
            TyKind::Tuple(tys) => tys.to_vec(),
            TyKind::Array(orig, _) => vec![orig],
            TyKind::Slice(orig) => vec![orig],
            TyKind::Ref(_, orig, _) => vec![orig],
            _ => Vec::new(),
        }
    }

    pub fn bool(tcx: ty::TyCtxt<'tcx>) -> Self {
        MostGenericTy(tcx.types.bool)
    }
}

impl<'tcx> From<MostGenericTy<'tcx>> for ty::Ty<'tcx> {
    fn from(value: MostGenericTy<'tcx>) -> Self {
        value.0
    }
}

pub fn to_placeholder<'tcx>(tcx: ty::TyCtxt<'tcx>, idx: Option<usize>) -> ty::Ty<'tcx> {
    let name = idx
        .map(|idx| format!("T{idx}"))
        .unwrap_or_else(|| String::from("T"));
    tcx.mk_ty_from_kind(TyKind::Param(ty::ParamTy {
        index: idx.unwrap_or_default() as u32,
        name: symbol::Symbol::intern(&name),
    }))
}

pub fn extract_type_params<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> (MostGenericTy<'tcx>, Vec<ty::Ty<'tcx>>) {
    let (generic_ty, arg_tys) = match *ty.kind() {
        TyKind::Adt(adt, args) => {
            let id = ty::List::identity_for_item(tcx, adt.did()).iter();
            let id = tcx.mk_args_from_iter(id);
            let ty = tcx.mk_ty_from_kind(TyKind::Adt(adt, id));
            (
                MostGenericTy(ty),
                args.into_iter().flat_map(ty::GenericArg::as_type).collect(),
            )
        }
        TyKind::Tuple(tys) => {
            let new_tys = tcx.mk_type_list_from_iter(
                (0..tys.len()).map(|index| to_placeholder(tcx, Some(index))),
            );
            let ty = tcx.mk_ty_from_kind(TyKind::Tuple(new_tys));
            (MostGenericTy(ty), tys.to_vec())
        }
        TyKind::Array(orig, val) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Array(ty, val));
            (MostGenericTy(ty), vec![orig])
        }
        TyKind::Slice(orig) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Slice(ty));
            (MostGenericTy(ty), vec![orig])
        }
        TyKind::Ref(r, orig, m) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Ref(r, ty, m));
            (MostGenericTy(ty), vec![orig])
        }
        _ => (MostGenericTy(ty), Vec::new()),
    };
    let arg_tys = arg_tys.into_iter().filter(|ty| !matches!(ty.kind(), ty::Param(_))).collect();
    (generic_ty, arg_tys)
}
