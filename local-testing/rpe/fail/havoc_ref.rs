fn set_zero(x: &mut i32) {
    *x = 0;
}
fn main() {
    let mut x = 1;
    set_zero(&mut x);
    assert!(x == 1);
}
