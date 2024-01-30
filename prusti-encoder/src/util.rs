use std::collections::BTreeMap;

use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::TaskEncoderDependencies;
use vir::{Caster, UnaryArity};

use crate::encoders::{snapshot::SnapshotEnc, GenericEnc};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MostGenericTy<'tcx>(ty::Ty<'tcx>);

impl<'tcx> MostGenericTy<'tcx> {
    pub fn kind(&self) -> &TyKind<'tcx> {
        self.0.kind()
    }

    pub fn tuple(arity: usize) -> Self {
        assert!(arity != 1);
        let tuple = vir::with_vcx(|vcx| {
            let new_tys = vcx.tcx.mk_type_list_from_iter(
                (0..arity).map(|index| to_placeholder(vcx.tcx, Some(index))),
            );
            vcx.tcx.mk_ty_from_kind(ty::TyKind::Tuple(new_tys))
        });
        MostGenericTy(tuple)
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
            TyKind::Bool => Vec::new(),
            TyKind::Int(_) => Vec::new(),
            TyKind::Uint(_) => Vec::new(),
            TyKind::Param(_) => Vec::new(),
            TyKind::Never => Vec::new(),
            other => todo!("generics for {:?}", other),
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
        TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Param(_) | TyKind::Never => {
            (MostGenericTy(ty), Vec::new())
        }
        _ => todo!("extract_type_params for {:?}", ty),
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
