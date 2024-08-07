use prusti_contracts::*;

#[requires(*x < 10)]
#[ensures(*x > old(*x))]
fn inc(x: &mut i32) {
    *x += 1;
    assert!(*x > old(*x));
}

fn main() {
}

