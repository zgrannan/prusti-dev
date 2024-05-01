use prusti_contracts::*;

#[pure]
fn return2() -> i32 {
    2
}

fn main(){
    let x = return2();
    assert!(x == 2);
}
