#![feature(core_intrinsics, rustc_attrs)]

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/assertfalse/main.dot")]
pub fn assertfalse() {
    assert!(false);
}

fn main(){}

