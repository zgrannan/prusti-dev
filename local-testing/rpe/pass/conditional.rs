#![feature(core_intrinsics, rustc_attrs)]
use prusti_contracts::*;

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/conditional/ret0.dot")]
#[ensures(b ==> result == 1)]
fn ret01(b: bool) -> u32 {
    if b { 1 } else { 0 }
}

fn main() {

}
