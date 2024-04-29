use crate::symbolic_execution::place::Place;
use crate::symbolic_execution::value::{SymValue, Constant};
use prusti_rustc_interface::middle::mir;
use std::collections::BTreeMap;


#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SymbolicHeap<'tcx>(BTreeMap<Place<'tcx>, SymValue<'tcx>>);

impl<'tcx> SymbolicHeap<'tcx> {

    pub fn check_eq_debug(&self, other: &Self) {
        for (p, v) in self.0.iter() {
            if !other.0.contains_key(&p) {
                panic!("Heap missing key: {:?}", p);
            }
            let other_v = other.0.get(&p).unwrap();
            if *v != *other_v {
                panic!("Heap value mismatch: {:?} {:?} vs {:?}", p, v, other_v);
            }
        }
        for (p, v) in other.0.iter() {
            if !self.0.contains_key(&p) {
                panic!("Heap missing key: {:?}", p);
            }
        }
    }

    pub fn new() -> Self {
        SymbolicHeap(BTreeMap::new())
    }

    pub fn insert(&mut self, place: Place<'tcx>, value: SymValue<'tcx>) {
        self.0.insert(place, value);
    }

    pub fn get(&self, place: &Place<'tcx>) -> Option<&SymValue<'tcx>> {
        self.0.get(&place)
    }

    pub fn take(&mut self, place: &Place<'tcx>) -> SymValue<'tcx> {
        self.0
            .remove(&place)
            .unwrap_or_else(|| panic!("{place:?} not found in heap {:#?}", self.0))
    }

    pub fn get_return_place_expr(&self) -> Option<&SymValue<'tcx>> {
        self.get(&mir::RETURN_PLACE.into())
    }

    pub fn encode_operand(&self, operand: &mir::Operand<'tcx>) -> SymValue<'tcx> {
        match *operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.get(&place.into()).unwrap().clone()
            }
            mir::Operand::Constant(box c) => SymValue::Constant(Constant(c.clone())),
        }
    }
}
