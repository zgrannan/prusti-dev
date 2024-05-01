#![feature(core_intrinsics, rustc_attrs)]

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/loop/main.dot")]
fn main() {
    let mut x = 0;
    while x < 10 {
        x += 1;
    }
    assert!(x >= 20)
}

