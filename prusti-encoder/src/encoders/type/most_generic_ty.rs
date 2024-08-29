use prusti_rustc_interface::{
    middle::ty::{self, TyKind, TypeAndMut},
    span::symbol,
};
use vir::{DomainParamData, NullaryArityAny};
/// The "most generic" version of a type is one that uses "identity
/// substitutions" for all type parameters. For example, the most generic
/// version of `Vec<u32>` is `Vec<T>`, the most generic version of
/// `Option<Vec<U>>` is `Option<T>`, etc.
///
/// To construct an instance, use [`extract_type_params`].
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MostGenericTy<'tcx>(ty::Ty<'tcx>);

impl<'tcx: 'vir, 'vir> MostGenericTy<'tcx> {
    pub fn get_vir_domain_ident(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>> {
        let base_name = self.get_vir_base_name(vcx);
        vir::DomainIdent::nullary(vir::vir_format_identifier!(vcx, "s_{base_name}"))
    }
}

impl<'tcx> MostGenericTy<'tcx> {
    pub fn get_vir_base_name(&self, vcx: &vir::VirCtxt<'tcx>) -> String {
        match self.kind() {
            TyKind::Bool => String::from("Bool"),
            TyKind::Char => String::from("Char"),
            TyKind::Int(kind) => format!("Int_{}", kind.name_str()),
            TyKind::Uint(kind) => format!("UInt_{}", kind.name_str()),
            TyKind::Float(kind) => format!("Float_{}", kind.name_str()),
            TyKind::Str => String::from("String"),
            TyKind::Adt(adt, _) => vcx.tcx().def_path_str(adt.did()),
            TyKind::Tuple(params) => format!("{}_Tuple", params.len()),
            TyKind::Never => String::from("Never"),
            TyKind::Ref(_, _, m) => {
                if m.is_mut() {
                    String::from("Ref_mutable")
                } else {
                    String::from("Ref_immutable")
                }
            }
            TyKind::RawPtr(type_and_mut) => {
                if type_and_mut.mutbl.is_mut() {
                    String::from("Ptr_mutable")
                } else {
                    String::from("Ptr_immutable")
                }
            }
            TyKind::Param(_) => String::from("Param"),
            TyKind::Array(..) => String::from("Array"),
            TyKind::Foreign(_) => todo!(),
            TyKind::Slice(_) => todo!(),
            TyKind::FnDef(_, _) => todo!(),
            TyKind::FnPtr(_) => String::from("FnPtr"),
            TyKind::Dynamic(_, _, _) => todo!(),
            TyKind::Closure(_, _) => String::from("Closure"),
            TyKind::Generator(_, _, _) => todo!(),
            TyKind::GeneratorWitness(_) => todo!(),
            TyKind::GeneratorWitnessMIR(_, _) => todo!(),
            TyKind::Alias(_, _) => todo!(),
            TyKind::Bound(_, _) => todo!(),
            TyKind::Placeholder(_) => todo!(),
            TyKind::Infer(_) => todo!(),
            TyKind::Error(_) => todo!(),
        }
    }

    pub fn is_generic(&self) -> bool {
        matches!(self.kind(), TyKind::Param(_))
    }

    pub fn kind(&self) -> &TyKind<'tcx> {
        self.0.kind()
    }

    pub fn tuple(arity: usize) -> Self {
        assert!(arity != 1);
        let tuple = vir::with_vcx(|vcx| {
            let new_tys = vcx.tcx().mk_type_list_from_iter(
                (0..arity).map(|index| to_placeholder(vcx.tcx(), Some(index))),
            );
            vcx.tcx().mk_ty_from_kind(ty::TyKind::Tuple(new_tys))
        });
        MostGenericTy(tuple)
    }

    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.0
    }

    pub fn generics(&self) -> Vec<&'tcx ty::ParamTy> {
        let as_param_ty = |ty: ty::Ty<'tcx>| match ty.kind() {
            TyKind::Param(p) => p,
            _ => unreachable!(),
        };
        match self.kind() {
            TyKind::Adt(_, args) => args
                .into_iter()
                .flat_map(ty::GenericArg::as_type)
                .map(as_param_ty)
                .collect(),
            TyKind::Tuple(tys) => tys.iter().map(as_param_ty).collect::<Vec<_>>(),
            TyKind::Array(orig, _) => vec![as_param_ty(*orig)],
            TyKind::Slice(orig) => vec![as_param_ty(*orig)],
            TyKind::Ref(_, orig, _) => vec![as_param_ty(*orig)],
            TyKind::RawPtr(type_and_mut) => vec![as_param_ty(type_and_mut.ty)],
            TyKind::Bool
            | TyKind::Char
            | TyKind::Float(_)
            | TyKind::Int(_)
            | TyKind::Never
            | TyKind::Param(_)
            | TyKind::Uint(_) => Vec::new(),
            TyKind::Closure(..) => vec![], // TODO
            TyKind::FnPtr(_) => vec![], // TODO
            other => todo!("generics for {:?}", other),
        }
    }
}

impl<'tcx> From<MostGenericTy<'tcx>> for ty::Ty<'tcx> {
    fn from(value: MostGenericTy<'tcx>) -> Self {
        value.0
    }
}

fn to_placeholder(tcx: ty::TyCtxt<'_>, idx: Option<usize>) -> ty::Ty<'_> {
    let name = idx
        .map(|idx| format!("T{idx}"))
        .unwrap_or_else(|| String::from("T"));
    tcx.mk_ty_from_kind(TyKind::Param(ty::ParamTy {
        index: idx.unwrap_or_default() as u32,
        name: symbol::Symbol::intern(&name),
    }))
}

pub fn extract_type_params<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> (MostGenericTy<'tcx>, Vec<ty::Ty<'tcx>>) {
    match *ty.kind() {
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
        TyKind::Ref(_, orig, m) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Ref(tcx.lifetimes.re_erased, ty, m));
            (MostGenericTy(ty), vec![orig])
        }
        TyKind::Param(_) => (MostGenericTy(to_placeholder(tcx, None)), Vec::new()),
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Never
        | TyKind::Str => (MostGenericTy(ty), Vec::new()),
        TyKind::RawPtr(type_and_mut) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::RawPtr(TypeAndMut {
                ty,
                mutbl: type_and_mut.mutbl,
            }));
            (MostGenericTy(ty), vec![type_and_mut.ty])
        }
        TyKind::Closure(def_id, substs) => {
            let id = ty::List::identity_for_item(tcx, def_id).iter();
            let id = tcx.mk_args_from_iter(id);
            let ty = tcx.mk_ty_from_kind(TyKind::Closure(def_id, id));
            (
                MostGenericTy(ty),
                substs
                    .into_iter()
                    .flat_map(ty::GenericArg::as_type)
                    .collect(),
            )
        }
        TyKind::Foreign(_) => todo!(),
        TyKind::FnDef(_, _) => todo!(),
        TyKind::FnPtr(_) => (MostGenericTy(ty), Vec::new()), // TODO,
        TyKind::Dynamic(_, _, _) => todo!(),
        TyKind::Generator(_, _, _) => todo!(),
        TyKind::GeneratorWitness(_) => todo!(),
        TyKind::GeneratorWitnessMIR(_, _) => todo!(),
        TyKind::Alias(_, _) => todo!(),
        TyKind::Bound(_, _) => todo!(),
        TyKind::Placeholder(_) => todo!(),
        TyKind::Infer(_) => todo!(),
        TyKind::Error(_) => todo!(),
    }
}
