use prusti_rustc_interface::{
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, ProjectionElem},
        ty,
    },
};
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Place<'tcx> {
    local: mir::Local,
    projection: Vec<ProjectionElem<mir::Local, ty::Ty<'tcx>>>,
}

impl<'tcx> From<mir::Local> for Place<'tcx> {
    fn from(value: mir::Local) -> Self {
        Place {
            local: value,
            projection: Vec::new(),
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for Place<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Place::new(place.local, place.projection.iter().collect())
    }
}

impl<'tcx> From<&mir::PlaceRef<'tcx>> for Place<'tcx> {
    fn from(value: &mir::PlaceRef<'tcx>) -> Self {
        Place::new(value.local, value.projection.into())
    }
}

impl<'tcx> Place<'tcx> {
    pub fn new(
        local: mir::Local,
        projection: Vec<ProjectionElem<mir::Local, ty::Ty<'tcx>>>,
    ) -> Self {
        Place { local, projection }
    }
}

fn hash<T: Hash>(t: T) -> u64 {
    let mut hasher = FxHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

impl<'tcx> PartialOrd for Place<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        hash(self).partial_cmp(&hash(other))
    }
}

impl<'tcx> Ord for Place<'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        hash(self).cmp(&hash(other))
    }
}
