use prusti_rustc_interface::{
    abi::VariantIdx,
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, ProjectionElem},
        ty::{self},
    },
    span::{def_id::DefId, DUMMY_SP},
};

use std::{
    cmp::Ordering,
    collections::BTreeMap,
    hash::{Hash, Hasher},
    rc::Rc,
};

use super::SymExArena;

#[derive(Debug)]
pub struct Ty<'tcx>(ty::Ty<'tcx>, Option<VariantIdx>);

impl<'tcx> Ty<'tcx> {
    pub fn new(ty: ty::Ty<'tcx>, variant_index: Option<VariantIdx>) -> Self {
        Ty(ty, variant_index)
    }
    pub fn variant_index(&self) -> Option<VariantIdx> {
        self.1
    }
    pub fn rust_ty(&self) -> ty::Ty<'tcx> {
        self.0
    }
}

pub trait SyntheticSymValueData<'sym, 'tcx>: Sized {
    fn subst(&self, arena: &'sym SymExArena, tcx: ty::TyCtxt<'tcx>, substs: &Substs<'sym, 'tcx, Self>) -> &'sym Self;
    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx>;
}

pub type SymValue<'sym, 'tcx, T> = &'sym SymValueData<'sym, 'tcx, T>;

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum SymValueData<'sym, 'tcx, T> {
    Var(usize, ty::Ty<'tcx>),
    Ref(SymValue<'sym, 'tcx, T>),
    Constant(Constant<'tcx>),
    CheckedBinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        SymValue<'sym, 'tcx, T>,
        SymValue<'sym, 'tcx, T>,
    ),
    BinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        SymValue<'sym, 'tcx, T>,
        SymValue<'sym, 'tcx, T>,
    ),
    UnaryOp(ty::Ty<'tcx>, mir::UnOp, SymValue<'sym, 'tcx, T>),
    Projection(
        ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        SymValue<'sym, 'tcx, T>,
    ),
    Aggregate(AggregateKind<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
    Discriminant(SymValue<'sym, 'tcx, T>),
    Synthetic(&'sym T),
}

pub type Substs<'sym, 'tcx, T> = BTreeMap<usize, SymValueData<'sym, 'tcx, T>>;

impl<'sym, 'tcx, T: SyntheticSymValueData<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            SymValueData::Var(_, ty) => Ty::new(*ty, None),
            SymValueData::Ref(val) => todo!(),
            SymValueData::Constant(c) => Ty::new(c.ty(), None),
            SymValueData::CheckedBinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueData::BinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueData::Projection(elem, val) => match elem {
                ProjectionElem::Deref => todo!(),
                ProjectionElem::Field(_, ty) => Ty::new(*ty, None),
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                ProjectionElem::Subslice { from, to, from_end } => todo!(),
                ProjectionElem::Downcast(_, vidx) => Ty::new(val.ty(tcx).rust_ty(), Some(*vidx)),
                ProjectionElem::OpaqueCast(_) => todo!(),
            },
            SymValueData::Aggregate(kind, _) => kind.ty(),
            SymValueData::Discriminant(sym_val) => {
                Ty::new(sym_val.ty(tcx).rust_ty().discriminant_ty(tcx), None)
            }
            SymValueData::UnaryOp(ty, op, val) => Ty::new(*ty, None),
            SymValueData::Synthetic(sym_val) => sym_val.ty(tcx),
        }
    }
}

impl<'sym, 'tcx, T: Clone + SyntheticSymValueData<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn subst(
        &'sym self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'sym Substs<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        match self {
            SymValueData::Var(idx, ty) => {
                if let Some(subst) = substs.get(&idx) {
                    assert_eq!(*ty, subst.ty(tcx).rust_ty());
                    subst
                } else {
                    self
                }
            }
            c @ SymValueData::Constant(_) => c,
            SymValueData::CheckedBinaryOp(ty, op, lhs, rhs) => {
                arena.alloc(SymValueData::CheckedBinaryOp(
                    *ty,
                    *op,
                    lhs.subst(arena, tcx, substs),
                    rhs.subst(arena, tcx, substs),
                ))
            }
            SymValueData::BinaryOp(ty, op, lhs, rhs) => arena.alloc(SymValueData::BinaryOp(
                *ty,
                *op,
                lhs.subst(arena, tcx, substs),
                rhs.subst(arena, tcx, substs),
            )),
            SymValueData::Projection(kind, val) => arena.alloc(SymValueData::Projection(
                *kind,
                val.subst(arena, tcx, substs),
            )),
            SymValueData::Aggregate(ty, vals) => {
                let vals = vals
                    .iter()
                    .map(|v| v.subst(arena, tcx, substs))
                    .collect::<Vec<_>>();
                arena.alloc(SymValueData::Aggregate(*ty, arena.alloc_slice(&vals)))
            }
            SymValueData::Discriminant(val) => {
                arena.alloc(SymValueData::Discriminant(val.subst(arena, tcx, substs)))
            }
            SymValueData::Ref(val) => arena.alloc(SymValueData::Ref(val.subst(arena, tcx, substs))),
            SymValueData::UnaryOp(ty, op, expr) => arena.alloc(SymValueData::UnaryOp(
                *ty,
                *op,
                expr.subst(arena, tcx, substs),
            )),
            SymValueData::Synthetic(sym_val) => arena.alloc(SymValueData::Synthetic(sym_val.subst(arena, tcx, substs))),
        }
    }
}

impl<'tcx> From<&Box<mir::Constant<'tcx>>> for Constant<'tcx> {
    fn from(c: &Box<mir::Constant<'tcx>>) -> Self {
        Constant(**c)
    }
}

impl<'tcx> From<mir::Constant<'tcx>> for Constant<'tcx> {
    fn from(c: mir::Constant<'tcx>) -> Self {
        Constant(c)
    }
}

#[derive(Clone, Debug, Hash)]
pub struct Constant<'tcx>(pub mir::Constant<'tcx>);

impl<'tcx> Constant<'tcx> {
    pub fn literal(&self) -> mir::ConstantKind<'tcx> {
        self.0.literal
    }

    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.0.literal.ty()
    }

    pub fn from_bool(tcx: ty::TyCtxt<'tcx>, b: bool) -> Self {
        Constant(mir::Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: mir::ConstantKind::from_bool(tcx, b),
        })
    }
}

impl<'tcx> Ord for Constant<'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

impl<'tcx> Eq for Constant<'tcx> {}

fn hash<T: Hash>(t: T) -> u64 {
    let mut hasher = FxHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

impl<'tcx> PartialEq for Constant<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        hash(self) == hash(other)
    }
}

impl<'tcx> PartialOrd for Constant<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        hash(self).partial_cmp(&hash(other))
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct AggregateKind<'tcx>(ty::Ty<'tcx>, Option<VariantIdx>);

impl<'tcx> AggregateKind<'tcx> {
    pub fn from_mir(kind: mir::AggregateKind<'tcx>, result_ty: ty::Ty<'tcx>) -> Self {
        let variant_idx = match kind {
            mir::AggregateKind::Adt(_, vidx, _, _, _) => match result_ty.kind() {
                ty::TyKind::Adt(def, _) if def.is_enum() => Some(vidx),
                _ => None,
            },
            _ => None,
        };
        AggregateKind(result_ty, variant_idx)
    }

    pub fn new(ty: ty::Ty<'tcx>, variant_idx: Option<VariantIdx>) -> Self {
        AggregateKind(ty, variant_idx)
    }

    pub fn ty(&self) -> Ty<'tcx> {
        Ty(self.0, self.1)
    }
}
