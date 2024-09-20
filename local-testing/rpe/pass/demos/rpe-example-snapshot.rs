fn main(){
    let mut x = 1;
    let mut y = 1;
    let mut rx = &mut x;
    let rx2 = &mut (*rx);
    rx = &mut y;
    let _ = *rx2;
}
