use std::collections::BTreeMap;

use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::TaskEncoderDependencies;
use vir::{Caster, UnaryArity, VirCtxt};

use crate::encoders::{
    domain::DomainEnc, snapshot::SnapshotEnc, EncodedTyParam, GenericEnc, GenericPredicateEnc,
    GenericSnapshotEnc,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MostGenericTy<'tcx>(ty::Ty<'tcx>);

impl<'tcx> MostGenericTy<'tcx> {
    pub fn kind(&self) -> &TyKind<'tcx> {
        self.0.kind()
    }

    pub fn with_normalized_param_name(&self, tcx: ty::TyCtxt<'tcx>) -> MostGenericTy<'tcx> {
        match *self.kind() {
            TyKind::Param(_) => MostGenericTy(to_placeholder(tcx, None)),
            _ => *self,
        }
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

pub fn get_viper_type_value<'vir, 'tcx>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir>,
    ty: ty::Ty<'tcx>,
) -> EncodedTyParam<'vir> {
    if let TyKind::Param(p) = ty.kind() {
        EncodedTyParam::from_param(
            vcx,
            p,
            deps.require_ref::<GenericEnc>(()).unwrap().type_snapshot,
        )
    } else {
        let (generic_ty, args) = extract_type_params(vcx.tcx, ty);
        let type_function = deps
            .require_ref::<DomainEnc>(generic_ty)
            .unwrap()
            .type_function;
        let args = args
            .into_iter()
            .map(|ty| get_viper_type_value(vcx, deps, ty).expr(vcx))
            .collect::<Vec<_>>();
        type_function.apply(vcx, &args).into()
    }
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
        TyKind::Ref(r, orig, m) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Ref(r, ty, m));
            (MostGenericTy(ty), vec![orig])
        }
        _ => (MostGenericTy(ty), Vec::new()),
    }
}

#[derive(Copy, Clone, Debug)]
pub struct CastFunctions<'vir> {
    pub upcast: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    pub downcast: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
}

pub struct TyMapCaster<'vir> {
    generic_ty: vir::Type<'vir>,
    cast_functions: BTreeMap<vir::Type<'vir>, CastFunctions<'vir>>,
}

impl<'vir> TyMapCaster<'vir> {
    pub fn new<'tcx: 'vir>(
        tys: Vec<ty::Ty<'tcx>>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Self {
        let generic_ty = deps.require_ref::<GenericEnc>(()).unwrap().param_snapshot;
        let cast_functions = tys
            .iter()
            .filter_map(|ty| {
                let enc = deps.require_ref::<SnapshotEnc>(*ty).unwrap();
                enc.generic_snapshot
                    .cast_functions
                    .map(|cast_functions| (enc.generic_snapshot.snapshot, cast_functions))
            })
            .collect();
        Self {
            generic_ty,
            cast_functions,
        }
    }
}

impl<'vir> Caster<'vir> for TyMapCaster<'vir> {
    fn is_generic(&self, ty: vir::Type<'vir>) -> bool {
        ty == self.generic_ty
    }

    fn upcast<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir vir::VirCtxt<'_>,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.cast_functions
            .get(&expr.ty())
            .unwrap()
            .upcast
            .apply(vcx, [expr])
    }

    fn downcast<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir vir::VirCtxt<'_>,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.cast_functions
            .get(&expr.ty())
            .unwrap()
            .downcast
            .apply(vcx, [expr])
    }
}
