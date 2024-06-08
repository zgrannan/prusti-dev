use std::collections::{btree_set::Iter, BTreeSet};

use super::value::{Substs, SymValue, SyntheticSymValue};
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{self, GenericArgsRef},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PathConditionPredicate<'tcx, T> {
    /// The compared-to expr is equal to the scalar interpreted as a
    /// value of the given type
    Eq(u128, ty::Ty<'tcx>),
    /// The compared-to expr is not equal to any of the scalars
    /// interpreted as a value of the given type
    Ne(Vec<u128>, ty::Ty<'tcx>),
    /// The postcondition of the function defined by the DefId, applied to the arguments
    /// The compared-to expr is the result of the fn
    Postcondition(DefId, GenericArgsRef<'tcx>, Vec<SymValue<'tcx, T>>),
}

impl<'tcx, T: Clone + SyntheticSymValue<'tcx>> PathConditionPredicate<'tcx, T> {
    pub fn subst(self, tcx: ty::TyCtxt<'tcx>, substs: &Substs<'tcx, T>) -> Self {
        match self {
            PathConditionPredicate::Eq(..) | PathConditionPredicate::Ne(..) => self,
            PathConditionPredicate::Postcondition(def_id, args, values) => {
                PathConditionPredicate::Postcondition(
                    def_id,
                    args,
                    values
                        .into_iter()
                        .map(|value| value.subst(tcx, substs))
                        .collect(),
                )
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PathConditionAtom<'tcx, T> {
    pub expr: SymValue<'tcx, T>,
    pub predicate: PathConditionPredicate<'tcx, T>,
}

impl<'tcx, T> PathConditionAtom<'tcx, T> {
    pub fn new(expr: SymValue<'tcx, T>, predicate: PathConditionPredicate<'tcx, T>) -> Self {
        PathConditionAtom { expr, predicate }
    }
}

impl<'tcx, T: Clone + SyntheticSymValue<'tcx>> PathConditionAtom<'tcx, T> {
    pub fn subst(self, tcx: ty::TyCtxt<'tcx>, substs: &Substs<'tcx, T>) -> Self {
        let expr = self.expr.subst(tcx, substs);
        let predicate = self.predicate.subst(tcx, substs);
        PathConditionAtom::new(expr, predicate)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PathConditions<'tcx, T> {
    pub atoms: BTreeSet<PathConditionAtom<'tcx, T>>,
}

impl <'tcx, T> PathConditions<'tcx, T> {
    pub fn new() -> Self {
        PathConditions {
            atoms: BTreeSet::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn iter(&self) -> Iter<'_, PathConditionAtom<'tcx, T>> {
        self.atoms.iter()
    }
}

impl<'tcx, T: Ord>  PathConditions<'tcx, T> {
    pub fn insert(&mut self, atom: PathConditionAtom<'tcx, T>) {
        self.atoms.insert(atom);
    }
}

impl<'tcx, T: Clone + Ord + SyntheticSymValue<'tcx>> PathConditions<'tcx, T> {

    pub fn subst(self, tcx: ty::TyCtxt<'tcx>, substs: &Substs<'tcx, T>) -> Self {
        let mut atoms = BTreeSet::new();
        for atom in &self.atoms {
            let expr = atom.expr.clone().subst(tcx, substs);
            let predicate = atom.predicate.clone();
            atoms.insert(PathConditionAtom::new(expr, predicate));
        }
        PathConditions { atoms }
    }
}
