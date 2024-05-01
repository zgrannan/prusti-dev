#![feature(core_intrinsics, rustc_attrs)]

use prusti_contracts::*;

enum IntOption {
    Some(i32),
    None
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/int-option-sound/foo.dot")]
fn foo(x: IntOption) -> i32 {
    let y = IntOption::Some(123);
    let ret = match x {
        IntOption::Some(y) => y,
        IntOption::None => 456
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn main() {

}
