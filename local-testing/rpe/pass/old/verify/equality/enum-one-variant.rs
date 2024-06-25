#![feature(core_intrinsics, rustc_attrs)]
use prusti_contracts::*;

#[derive(Clone,PartialEq,Eq)]
enum A {
    U(u32),
}

#[requires(_x == _y)]
#[ensures(result == 17)]
#[rustc_mir(borrowck_graphviz_postflow="log/analysis/equality/enum-one-variant.dot")]
fn test(_x: &A, _y: &A) -> i32 {
    assert!(_x == _y);
    17
}

fn main() {
}
