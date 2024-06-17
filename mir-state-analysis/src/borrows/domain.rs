use prusti_rustc_interface::{
    dataflow::{JoinSemiLattice, AnalysisDomain},
    borrowck::consumers::BorrowIndex,
    data_structures::fx::{FxHashMap, FxHashSet},
};

impl JoinSemiLattice for BorrowsDomain {
    fn join(&mut self, other: &Self) -> bool {
    let mut changed = false;
    for borrow in &other.live_borrows {
        if self.live_borrows.insert(*borrow) {
            changed = true;
        }
    }
    changed
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsDomain {
    pub live_borrows: FxHashSet<BorrowIndex>,
}

impl BorrowsDomain {
    pub fn new() -> Self {
        Self {
            live_borrows: FxHashSet::default(),
        }
    }

    pub fn add_borrow(&mut self, borrow: BorrowIndex) {
        self.live_borrows.insert(borrow);
    }

    pub fn remove_borrow(&mut self, borrow: &BorrowIndex) {
        self.live_borrows.remove(borrow);
    }
}
