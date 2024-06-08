// ZG: Todo

#![feature(core_intrinsics, rustc_attrs)]

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/equality/empty-tuple/main.dot")]
fn main() {
    let _a = ();
    let _b = ();
    assert!(_a == _b);
}
