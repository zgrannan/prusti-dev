fn main() {
    let mut x = 0;
    let mut y = 1;
    let mut a = &mut x;
    let mut b = &mut (*a);
    let mut c = &mut (*b);
    let mut d = &mut (*c);
    while false {
        c = &mut *a;
        b = &mut *c;
        d = &mut *b;
    }
    let e = *b;
}
