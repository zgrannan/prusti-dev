fn go(mut t0: u32) {
    let mut x = &mut t0;
    let tmp = x;
    *tmp = 0;
    assert!(t0 == 0);
}

fn main() {}
