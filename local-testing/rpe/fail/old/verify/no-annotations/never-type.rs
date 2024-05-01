#![feature(core_intrinsics, rustc_attrs)]
#![feature(never_type)]

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/never_type/diverge.dot")]
fn diverging() -> ! {
    panic!();  //~ ERROR panic!(..) statement might be reachable
}

fn main() {}
