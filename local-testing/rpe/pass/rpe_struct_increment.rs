#![feature(core_intrinsics, rustc_attrs)]
use prusti_contracts::*;

struct Point {x: u32, y: u32 }

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/increment/shiftright.dot")]
#[requires(pt.x < 100)]
fn shift_right(mut pt: Point) -> Point {
   pt.x += 1;
   pt
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/increment/client.dot")]
fn client() -> Point {
   shift_right(Point { x: 1, y: 2 })
}

fn main(){

}
