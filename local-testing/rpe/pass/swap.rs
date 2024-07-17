fn swap(mut t0: u32, mut t1: u32, b: bool) {
    let t0_start = t0;
    let mut x = &mut t0;
    let mut y = &mut t1;
    if b {
        let tmp = x;
        x = y;
        y = tmp;
    }
    let last_usage_x = x;
    let last_usage_y = y;
}

fn main() {}
