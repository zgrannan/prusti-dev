#![feature(core_intrinsics, rustc_attrs)]
use prusti_contracts::*;

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/increment/ret1.dot")]
#[ensures(result == 1)]
fn ret1() -> u32 {
   let mut x = 0;
   x += 1;
   x
}

fn main() {

}
