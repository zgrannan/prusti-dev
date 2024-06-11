use debug_info::DebugInfo;
use prusti_rustc_interface::{
    abi::VariantIdx,
    const_eval::interpret::ConstValue,
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

pub trait SyntheticSymValue<'sym, 'tcx>: Sized {
    fn optimize(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Self;
    fn subst(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &Substs<'sym, 'tcx, Self>,
    ) -> Self;
    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx>;
}

pub type SymValue<'sym, 'tcx, T> = &'sym SymValueData<'sym, 'tcx, T>;

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct SymValueData<'sym, 'tcx, T> {
    pub kind: SymValueKind<'sym, 'tcx, T>,
    pub debug_info: DebugInfo<'sym>,
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn new(kind: SymValueKind<'sym, 'tcx, T>, arena: &'sym SymExArena) -> Self {
        SymValueData {
            kind,
            debug_info: DebugInfo::new(|t| arena.alloc(t)),
        }
    }

    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        self.kind.ty(tcx)
    }
}

impl<'sym, 'tcx, T: std::fmt::Display> std::fmt::Display for SymValueData<'sym, 'tcx, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            SymValueKind::Var(idx, ty) => write!(f, "(s{}: {})", idx, ty),
            SymValueKind::Ref(_, t) => {
                write!(f, "(&{})", t)
            }
            SymValueKind::Constant(c) => write!(f, "{:?}", c),
            SymValueKind::CheckedBinaryOp(_, _, _, _) => todo!(),
            SymValueKind::BinaryOp(_, op, lhs, rhs) => {
                write!(f, "({} {:?} {})", lhs, op, rhs)
            }
            SymValueKind::UnaryOp(_, op, expr) => {
                write!(f, "({:?} {})", op, expr)
            }
            SymValueKind::Projection(kind, value) => match &kind {
                ProjectionElem::Deref => write!(f, "*({})", value),
                ProjectionElem::Field(_, _) => todo!(),
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                ProjectionElem::Subslice { from, to, from_end } => todo!(),
                ProjectionElem::Downcast(_, _) => todo!(),
                ProjectionElem::OpaqueCast(_) => todo!(),
            },
            SymValueKind::Aggregate(kind, values) => {
                let values_str = values
                    .iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "(compose [{}] to {:?})", values_str, kind)
            }
            SymValueKind::Discriminant(_) => todo!(),
            SymValueKind::Synthetic(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum SymValueKind<'sym, 'tcx, T> {
    Var(usize, ty::Ty<'tcx>),
    Ref(ty::Ty<'tcx>, SymValue<'sym, 'tcx, T>),
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
    Synthetic(T),
}

#[derive(Debug)]
pub struct Substs<'sym, 'tcx, T>(BTreeMap<usize, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> Substs<'sym, 'tcx, T> {
    pub fn from_iter(iter: impl Iterator<Item = (usize, SymValue<'sym, 'tcx, T>)>) -> Self {
        Substs(iter.collect())
    }
    pub fn get(&self, idx: &usize) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.get(idx).copied()
    }
    pub fn singleton(idx: usize, val: SymValue<'sym, 'tcx, T>) -> Self {
        Substs(std::iter::once((idx, val)).collect())
    }
}

pub trait SymValueTransformer<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> {
    fn transform_var(
        &mut self,
        arena: &'sym SymExArena,
        idx: usize,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_var(idx, ty)
    }
    fn transform_ref(
        &mut self,
        arena: &'sym SymExArena,
        ty: ty::Ty<'tcx>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_ref(ty, val)
    }
    fn transform_constant(
        &mut self,
        arena: &'sym SymExArena,
        c: &'sym Constant<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_constant(c.clone())
    }
    fn transform_checked_binary_op(
        &mut self,
        arena: &'sym SymExArena,
        ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_checked_bin_op(ty, op, lhs, rhs)
    }
    fn transform_binary_op(
        &mut self,
        arena: &'sym SymExArena,
        ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_bin_op(ty, op, lhs, rhs)
    }
    fn transform_unary_op(
        &mut self,
        arena: &'sym SymExArena,
        ty: ty::Ty<'tcx>,
        op: mir::UnOp,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_unary_op(ty, op, val)
    }
    fn transform_projection(
        &mut self,
        arena: &'sym SymExArena,
        elem: ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_projection(elem, val)
    }
    fn transform_aggregate(
        &mut self,
        arena: &'sym SymExArena,
        kind: AggregateKind<'tcx>,
        vals: &'sym [SymValue<'sym, 'tcx, T>],
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_aggregate(kind, vals)
    }
    fn transform_discriminant(
        &mut self,
        arena: &'sym SymExArena,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_discriminant(val)
    }
    fn transform_synthetic(&mut self, arena: &'sym SymExArena, s: T) -> SymValue<'sym, 'tcx, T>;
}

impl<'sym, 'tcx, T: Copy + SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn apply_transformer<F>(
        &'sym self,
        arena: &'sym SymExArena,
        transformer: &mut F,
    ) -> SymValue<'sym, 'tcx, T>
    where
        F: SymValueTransformer<'sym, 'tcx, T>,
    {
        match &self.kind {
            SymValueKind::Var(idx, ty, ..) => transformer.transform_var(arena, *idx, *ty),
            SymValueKind::Ref(ty, val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_ref(arena, *ty, transformed_val)
            }
            SymValueKind::Constant(c) => transformer.transform_constant(arena, c),
            SymValueKind::CheckedBinaryOp(ty, op, lhs, rhs) => {
                let transformed_lhs = lhs.apply_transformer(arena, transformer);
                let transformed_rhs = rhs.apply_transformer(arena, transformer);
                transformer.transform_checked_binary_op(
                    arena,
                    *ty,
                    *op,
                    transformed_lhs,
                    transformed_rhs,
                )
            }
            SymValueKind::BinaryOp(ty, op, lhs, rhs) => {
                let transformed_lhs = lhs.apply_transformer(arena, transformer);
                let transformed_rhs = rhs.apply_transformer(arena, transformer);
                transformer.transform_binary_op(arena, *ty, *op, transformed_lhs, transformed_rhs)
            }
            SymValueKind::UnaryOp(ty, op, val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_unary_op(arena, *ty, *op, transformed_val)
            }
            SymValueKind::Projection(elem, val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_projection(arena, *elem, transformed_val)
            }
            SymValueKind::Aggregate(kind, vals) => {
                let transformed_vals: Vec<SymValue<'sym, 'tcx, T>> = vals
                    .iter()
                    .map(|v| v.apply_transformer(arena, transformer))
                    .collect();
                transformer.transform_aggregate(arena, *kind, arena.alloc_slice(&transformed_vals))
            }
            SymValueKind::Discriminant(val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_discriminant(arena, transformed_val)
            }
            SymValueKind::Synthetic(s) => transformer.transform_synthetic(arena, *s),
        }
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> SymValueKind<'sym, 'tcx, T> {
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            SymValueKind::Var(_, ty, ..) => Ty::new(*ty, None),
            SymValueKind::Ref(ty, _) => Ty::new(*ty, None),
            SymValueKind::Constant(c) => Ty::new(c.ty(), None),
            SymValueKind::CheckedBinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueKind::BinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueKind::Projection(elem, val) => match elem {
                ProjectionElem::Deref => {
                    if let ty::TyKind::Ref(_, ty, _) = val.kind.ty(tcx).rust_ty().kind() {
                        Ty::new(*ty, None)
                    } else {
                        unreachable!()
                    }
                }
                ProjectionElem::Field(_, ty) => Ty::new(*ty, None),
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                ProjectionElem::Subslice { from, to, from_end } => todo!(),
                ProjectionElem::Downcast(_, vidx) => {
                    Ty::new(val.kind.ty(tcx).rust_ty(), Some(*vidx))
                }
                ProjectionElem::OpaqueCast(_) => todo!(),
            },
            SymValueKind::Aggregate(kind, _) => kind.ty(),
            SymValueKind::Discriminant(sym_val) => {
                Ty::new(sym_val.kind.ty(tcx).rust_ty().discriminant_ty(tcx), None)
            }
            SymValueKind::UnaryOp(ty, op, val) => Ty::new(*ty, None),
            SymValueKind::Synthetic(sym_val) => sym_val.ty(tcx),
        }
    }
}

struct SubstsTransformer<'substs, 'sym, 'tcx, T>(ty::TyCtxt<'tcx>, &'substs Substs<'sym, 'tcx, T>);

impl<'substs, 'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> SymValueTransformer<'sym, 'tcx, T>
    for SubstsTransformer<'substs, 'sym, 'tcx, T>
{
    fn transform_var(
        &mut self,
        arena: &'sym SymExArena,
        idx: usize,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.1.get(&idx).unwrap_or(&arena.mk_var(idx, ty))
    }

    fn transform_synthetic(&mut self, arena: &'sym SymExArena, s: T) -> SymValue<'sym, 'tcx, T> {
        arena.mk_synthetic(s.subst(arena, self.0, self.1))
    }
}

impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn subst<'substs>(
        &'sym self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.apply_transformer(arena, &mut SubstsTransformer(tcx, substs))
    }
}

struct OptimizingTransformer<'tcx>(ty::TyCtxt<'tcx>);

impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx>> SymValueTransformer<'sym, 'tcx, T>
    for OptimizingTransformer<'tcx>
{
    fn transform_synthetic(&mut self, arena: &'sym SymExArena, s: T) -> SymValue<'sym, 'tcx, T> {
        arena.mk_synthetic(s.optimize(arena, self.0))
    }

    fn transform_projection(
        &mut self,
        arena: &'sym SymExArena,
        elem: ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        base: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        match elem {
            ProjectionElem::Deref => {
                if let SymValueKind::Ref(_, inner) = base.kind {
                    inner
                } else {
                    arena.mk_projection(elem, base.optimize(arena, self.0))
                }
            }
            _ => arena.mk_projection(elem, base.optimize(arena, self.0)),
        }
    }
}

impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn optimize(
        &'sym self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.apply_transformer(arena, &mut OptimizingTransformer(tcx))
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
    pub fn from_u32(u32: u32, ty: ty::Ty<'tcx>) -> Self {
        Constant(mir::Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: mir::ConstantKind::from_value(ConstValue::from_u64(u32 as u64), ty),
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
