use prusti_contracts::*;

/// Example 1 / Figure 1 from the paper "RustHorn: CHC-based Verification for Rust Programs"
/// authored by Yusuke Matsushita, Takeshi Tsukada, and Naoki Kobayashi

#[after_expiry(if old(*ma >= *mb) {
        (*ma == before_expiry(*result))
    } else {
        true
    })]
fn take_max<'a>(ma: &'a mut i32, mb: &'a mut i32) -> &'a mut i32 {
    ma
}

#[ensures(result == true)]
fn inc_max() -> bool {
    let mut a = 2;
    let mut b = 1;
    let mc = take_max(&mut a, &mut b);
    *mc = 3;
    a == 3
}

fn main() {}
