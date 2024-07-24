fn outlives<'a: 'b, 'b>(x: &'a mut i32, y: &'b mut i32) -> &'a mut i32 {
    x
}

fn main() {
    let mut x = 5;
    let mut y = 6;
    let z = outlives(&mut x, &mut y);
    *z = 1;
    y = x;
}
