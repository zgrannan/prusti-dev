fn f(mut x: i32, mut y: i32) {
    let r: &mut i32;
    if x > y {
        r = &mut x;
    } else {
        r = &mut y;
    }
    *r = 3;
}

fn main(){
}
