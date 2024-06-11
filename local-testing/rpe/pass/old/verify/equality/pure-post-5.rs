use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
#[requires(_x != _y)]
#[ensures(result != _y)]
fn first(_x: A, _y: A) -> A {
    _x
}

fn main() {
}
