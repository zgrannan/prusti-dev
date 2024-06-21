#![feature(core_intrinsics, rustc_attrs)]
#[rustc_mir(borrowck_graphviz_postflow="simpleref.dot")]
fn main() {
    let mut x = 1;
    let rx = &mut x;
    *rx += 1;
    assert!(x == 2);
}
