fn main() {
    let mut x = 1;
    let mut y = 2;
    let mut rx = &mut x;
    if true {
        rx = &mut y;
    }
}
