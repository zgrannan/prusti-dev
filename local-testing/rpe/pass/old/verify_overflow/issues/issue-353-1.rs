use prusti_contracts::*;
use std::collections::HashSet;
use std::hash::Hash;

struct WrappedHashSet{
    set: u32
}

impl WrappedHashSet{

    #[pure]
    #[trusted]
    fn is_empty(&self) -> bool {
        todo!()
    }

    #[trusted]
    #[ensures(self.is_empty())]
    fn clear(&mut self) {
    }

}

// Taken from Meirim, Filipe, Mário Pereira, and Carla Ferreira.
// "CISE3: Verifying Weakly Consistent Applications with Why3." arXiv preprint arXiv:2010.06622 (2020).
struct RemoveWinsSet{
    remove_wins_adds: WrappedHashSet,
}

impl RemoveWinsSet{

    #[ensures(self.remove_wins_adds.is_empty())]
    fn empty_set(&mut self) {
        self.remove_wins_adds.clear();
    }

}

#[trusted]
fn main() {}
