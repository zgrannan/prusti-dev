use std::rc::Rc;

use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::BorrowIndex
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir,
};

use crate::utils::Place;

impl<'tcx> JoinSemiLattice for BorrowsDomain<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for borrow in &other.live_borrows {
            if self.live_borrows.insert(borrow.clone()) {
                changed = true;
            }
        }
        for region_abstraction in &other.region_abstractions {
            if !self.region_abstractions.contains(region_abstraction) {
                self.region_abstractions.push(region_abstraction.clone());
                changed = true;
            }
        }
        changed
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RegionAbstraction<'tcx> {
    pub loans_in: FxHashSet<mir::Place<'tcx>>,
    pub loans_out: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> RegionAbstraction<'tcx> {
    pub fn new() -> Self {
        Self {
            loans_in: FxHashSet::default(),
            loans_out: FxHashSet::default(),
        }
    }

    pub fn add_loan_in(&mut self, loan: mir::Place<'tcx>) {
        self.loans_in.insert(loan);
    }

    pub fn add_loan_out(&mut self, loan: mir::Place<'tcx>) {
        self.loans_out.insert(loan);
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Borrow<'tcx> {
    Rustc(BorrowIndex),
    PCS {
        borrowed_place: Place<'tcx>,
        assigned_place: Place<'tcx>
    }
}

impl<'tcx> Borrow<'tcx> {
    pub fn assigned_place(&self, borrow_set: &Rc<BorrowSet<'tcx>>) -> Place<'tcx> {
        match self {
            Borrow::Rustc(borrow_index) => borrow_set[*borrow_index].assigned_place.into(),
            Borrow::PCS { borrowed_place, assigned_place } => *assigned_place,
        }
    }

    pub fn borrowed_place(&self, borrow_set: &Rc<BorrowSet<'tcx>>) -> Place<'tcx> {
        match self {
            Borrow::Rustc(borrow_index) => borrow_set[*borrow_index].borrowed_place.into(),
            Borrow::PCS { borrowed_place, assigned_place } => *borrowed_place,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsDomain<'tcx> {
    pub live_borrows: FxHashSet<Borrow<'tcx>>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
}

impl<'tcx> BorrowsDomain<'tcx> {
    pub fn new() -> Self {
        Self {
            live_borrows: FxHashSet::default(),
            region_abstractions: vec![],
        }
    }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        if !self.region_abstractions.contains(&abstraction) {
            self.region_abstractions.push(abstraction);
        }
    }

    pub fn add_borrow(&mut self, borrow: Borrow<'tcx>) {
        self.live_borrows.insert(borrow);
    }

    pub fn add_rustc_borrow(&mut self, borrow: BorrowIndex) {
        self.live_borrows.insert(Borrow::Rustc(borrow));
    }

    pub fn remove_borrow(&mut self, borrow: &BorrowIndex) {
        self.live_borrows.remove(&Borrow::Rustc(*borrow));
    }
}
