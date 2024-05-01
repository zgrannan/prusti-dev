use std::collections::{btree_set::Iter, BTreeMap, BTreeSet};

use super::value::SymValue;
use prusti_rustc_interface::{hir::def_id::DefId, middle::ty};

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PathConditionPredicate<'tcx> {
    /// The compared-to expr is equal to the scalar interpreted as a
    /// value of the given type
    Eq(u128, ty::Ty<'tcx>),
    /// The compared-to expr is not equal to any of the scalars
    /// interpreted as a value of the given type
    Ne(Vec<u128>, ty::Ty<'tcx>),
    /// The postcondition of the function defined by the DefId, applied to the arguments
    /// The compared-to expr is the result of the fn
    Postcondition(DefId, Vec<SymValue<'tcx>>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PathConditionAtom<'tcx> {
    pub expr: SymValue<'tcx>,
    pub predicate: PathConditionPredicate<'tcx>,
}

impl<'tcx> PathConditionAtom<'tcx> {
    pub fn new(expr: SymValue<'tcx>, predicate: PathConditionPredicate<'tcx>) -> Self {
        PathConditionAtom { expr, predicate }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PathConditions<'tcx> {
    pub atoms: BTreeSet<PathConditionAtom<'tcx>>,
}

impl<'tcx> PathConditions<'tcx> {
    pub fn new() -> Self {
        PathConditions {
            atoms: BTreeSet::new(),
        }
    }

    pub fn insert(&mut self, atom: PathConditionAtom<'tcx>) {
        self.atoms.insert(atom);
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn iter(&self) -> Iter<'_, PathConditionAtom<'tcx>> {
        self.atoms.iter()
    }
}
