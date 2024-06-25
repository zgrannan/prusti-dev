// PCS
use prusti_contracts::*;

#[derive(Clone, PartialEq, Eq)]
struct A<T> {
    i: i32,
    t: T,
}

#[pure]
fn get_value<T>(_x: &A<T>) -> i32 {
    _x.i
}

#[ensures(result == 1)]
fn test_eq_in_code(_a: &A<i32>, _b: &A<i32>) -> i32 {
    if *_a == *_b {
        if get_value(_a) == get_value(_b) {
            1
        } else {
            0
        }
    } else {
        1
    }
}

fn main() {
}
