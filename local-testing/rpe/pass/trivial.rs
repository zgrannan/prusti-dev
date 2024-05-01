#![feature(core_intrinsics, rustc_attrs)]
use prusti_contracts::*;

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/trivial/ret0.dot")]
#[ensures(result == 0)]
fn ret0() -> u32 {
    0
}

fn main() {

}
