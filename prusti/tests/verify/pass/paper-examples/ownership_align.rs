#![feature(box_syntax)]

extern crate prusti_contracts;

struct Point {
  x: i32, y: i32
}

#[ensures="old((*p).x + s) == (*result).x"]
#[ensures="old((*p).y) == (*result).y"]
fn shift_x(p: Box<Point>, s:i32) -> Box<Point> {
  box Point { x: (*p).x + s, y: (*p).y }
}

fn compress(mut segm: (Box<Point>, Box<Point>))
                    -> (Box<Point>, Box<Point>) {
  let mut end = segm.1; // move assignment ~\label{line:move}~
  // segm.1 is now inaccessible  ~\label{line:moved}~
  let diff = (*segm.0).x - (*end).x + 1;
  end = shift_x(end, diff); //~\label{line:call}~
  segm.1 = end; // ~\label{line:moveback}~
  // end is now inaccessible
  assert!((*segm.0).x < (*segm.1).x); //~\label{line:assert}~
  segm
}

fn main() {}
