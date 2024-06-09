use std::collections::{btree_set::Iter, BTreeSet};

use super::{
    value::{Substs, SymValue, SymValueData, SyntheticSymValueData},
    SymExArena,
};
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{self, GenericArgsRef},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PathConditionPredicate<'sym, 'tcx, T> {
    /// The compared-to expr is equal to the scalar interpreted as a
    /// value of the given type
    Eq(u128, ty::Ty<'tcx>),
    /// The compared-to expr is not equal to any of the scalars
    /// interpreted as a value of the given type
    Ne(Vec<u128>, ty::Ty<'tcx>),
    /// The postcondition of the function defined by the DefId, applied to the arguments
    /// The compared-to expr is the result of the fn
    Postcondition(DefId, GenericArgsRef<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
}

impl<'sym, 'tcx, T: Clone + SyntheticSymValueData<'sym, 'tcx>> PathConditionPredicate<'sym, 'tcx, T> {
    pub fn subst(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'sym Substs<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            PathConditionPredicate::Eq(..) | PathConditionPredicate::Ne(..) => self,
            PathConditionPredicate::Postcondition(def_id, args, values) => {
                PathConditionPredicate::Postcondition(
                    def_id,
                    args,
                    arena.alloc_slice(
                        &values
                            .iter()
                            .map(|value| value.subst(arena, tcx, substs))
                            .collect::<Vec<_>>(),
                    ),
                )
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PathConditionAtom<'sym, 'tcx, T> {
    pub expr: SymValue<'sym, 'tcx, T>,
    pub predicate: PathConditionPredicate<'sym, 'tcx, T>,
}

impl<'sym, 'tcx, T> PathConditionAtom<'sym, 'tcx, T> {
    pub fn new(
        expr: SymValue<'sym, 'tcx, T>,
        predicate: PathConditionPredicate<'sym, 'tcx, T>,
    ) -> Self {
        PathConditionAtom { expr, predicate }
    }
}

impl<'sym, 'tcx, T: Clone + SyntheticSymValueData<'sym, 'tcx>> PathConditionAtom<'sym, 'tcx, T> {
    pub fn subst(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'sym Substs<'sym, 'tcx, T>,
    ) -> Self {
        let expr = self.expr.subst(arena, tcx, substs);
        let predicate = self.predicate.subst(arena, tcx, substs);
        PathConditionAtom::new(expr, predicate)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PathConditions<'sym, 'tcx, T> {
    pub atoms: BTreeSet<PathConditionAtom<'sym, 'tcx, T>>,
}

impl<'sym, 'tcx, T> PathConditions<'sym, 'tcx, T> {
    pub fn new() -> Self {
        PathConditions {
            atoms: BTreeSet::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn iter(&self) -> Iter<'_, PathConditionAtom<'sym, 'tcx, T>> {
        self.atoms.iter()
    }
}

impl<'sym, 'tcx, T: Ord> PathConditions<'sym, 'tcx, T> {
    pub fn insert(&mut self, atom: PathConditionAtom<'sym, 'tcx, T>) {
        self.atoms.insert(atom);
    }
}

impl<'sym, 'tcx, T: Clone + Ord + SyntheticSymValueData<'sym, 'tcx>> PathConditions<'sym, 'tcx, T> {
    pub fn subst(
        self,
        arena: &'sym SymExArena,
        tcx: ty::TyCtxt<'tcx>,
        substs: &'sym Substs<'sym, 'tcx, T>,
    ) -> Self {
        let mut atoms = BTreeSet::new();
        for atom in &self.atoms {
            let expr = atom.expr.subst(arena, tcx, substs);
            let predicate = atom.predicate.clone().subst(arena, tcx, substs);
            atoms.insert(PathConditionAtom::new(expr, predicate));
        }
        PathConditions { atoms }
    }
}
