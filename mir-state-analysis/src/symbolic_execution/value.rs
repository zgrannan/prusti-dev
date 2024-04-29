use prusti_rustc_interface::{
    abi::{FieldIdx, VariantIdx, FIRST_VARIANT},
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, Place, ProjectionElem},
        ty::{self},
    },
};

use std::{
    cmp::Ordering, collections::BTreeMap, hash::{Hash, Hasher}, marker::PhantomData
};

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

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum SymValue<'tcx> {
    Var(usize, ty::Ty<'tcx>),
    Ref(Box<SymValue<'tcx>>),
    Constant(Constant<'tcx>),
    CheckedBinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        Box<SymValue<'tcx>>,
        Box<SymValue<'tcx>>,
    ),
    BinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        Box<SymValue<'tcx>>,
        Box<SymValue<'tcx>>,
    ),
    Projection(
        ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        Box<SymValue<'tcx>>,
    ),
    Aggregate(AggregateKind<'tcx>, Vec<SymValue<'tcx>>),
    Discriminant(Box<SymValue<'tcx>>),
}

pub type Substs<'tcx> = BTreeMap<usize, SymValue<'tcx>>;

impl<'tcx> SymValue<'tcx> {
    pub fn subst(self, tcx: ty::TyCtxt<'tcx>, substs: &Substs<'tcx>) -> Self {
        eprintln!("subst {:?} with substs: {:?}", self, substs);
        match self {
            SymValue::Var(idx, ty) => {
                assert_eq!(ty, substs[&idx].ty(tcx).rust_ty());
                substs[&idx].clone()
            }
            c @ SymValue::Constant(_) => c,
            SymValue::CheckedBinaryOp(ty, op, lhs, rhs) => SymValue::CheckedBinaryOp(
                ty,
                op,
                Box::new(lhs.subst(tcx, substs)),
                Box::new(rhs.subst(tcx, substs)),
            ),
            SymValue::BinaryOp(ty, op, lhs, rhs) => SymValue::BinaryOp(
                ty,
                op,
                Box::new(lhs.subst(tcx, substs)),
                Box::new(rhs.subst(tcx, substs)),
            ),
            SymValue::Projection(kind, val) => {
                SymValue::Projection(kind, Box::new(val.subst(tcx, substs)))
            }
            SymValue::Aggregate(ty, vals) => {
                let vals = vals.into_iter().map(|v| v.subst(tcx, substs)).collect();
                SymValue::Aggregate(ty, vals)
            }
            SymValue::Discriminant(val) => SymValue::Discriminant(Box::new(val.subst(tcx, substs))),
            SymValue::Ref(val) => SymValue::Ref(Box::new(val.subst(tcx, substs))),
        }
    }
}

impl<'tcx> SymValue<'tcx> {
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            SymValue::Var(_, ty) => Ty::new(*ty, None),
            SymValue::Ref(val) => todo!(),
            SymValue::Constant(c) => Ty::new(c.ty(), None),
            SymValue::CheckedBinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValue::BinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValue::Projection(elem, val) => match elem {
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
            SymValue::Aggregate(kind, _) => kind.ty(),
            SymValue::Discriminant(sym_val) => {
                Ty::new(sym_val.ty(tcx).rust_ty().discriminant_ty(tcx), None)
            }
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

#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
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
