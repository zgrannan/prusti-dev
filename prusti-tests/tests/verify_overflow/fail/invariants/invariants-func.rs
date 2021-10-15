extern crate prusti_contracts;
use prusti_contracts::*;

// precondition inhale

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

fn print_percentage(percentage: &Percentage){
}

#[requires(percentage.value >= 10)]
fn adjust_percentage(percentage: &mut Percentage, flag: bool) {
   let mut f0 = flag;
   if flag {
       percentage.value += 10; // temporarily break invariant
       f0 = false;
   } else {
       percentage.value = 120; // temporarily break invariant
       f0 = true;
   }

   print_percentage(percentage); //~ ERROR  precondition

   if f0 {
       percentage.value /= 2; // restore invariant
   } else {
       percentage.value -= 10; // restore invariant
   }
}

fn main() {}
