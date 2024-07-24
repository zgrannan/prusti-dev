#![feature(core_intrinsics, rustc_attrs)]
struct Pair<'x>(&'x mut i32, &'x mut i32);

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/swap.dot")]
fn swap<'c:'r, 'r>(mut p: Pair<'c>) -> Pair<'r> {
    let p1 = &mut *p.1;
    let p0 = &mut *p.0;
    *p0 = 3;
    p.0 = p1;
    p.1 = p0;
    p
}

fn main(){}
