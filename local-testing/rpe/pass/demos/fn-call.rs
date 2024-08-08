fn fst<'a>(x: &'a mut u32, y: &'a mut u32) -> &'a mut u32 {
    x
}

fn main(){
    let mut x = 0;
    let mut y = 0;
    let mut rx = &mut x;
    let mut ry = &mut y;
    let r = fst(rx, ry);
    let rr = &mut (*r);
    *rr = 1;
    let z = x;
}
