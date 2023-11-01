#![allow(dead_code)]
use prusti_contracts::*;

#[resource_kind]
struct Money();

#[invariant_twostate(
    holds(Money()) - old(holds(Money())) ==
    PermAmount::from(self.balance() - old(self.balance()))
)]
trait Bank {

    #[pure]
    fn balance(&self) -> u32;

    #[ensures(resource(Money(), amt))]
    fn deposit(&mut self, amt: u32);

    #[requires(resource(Money(), amt))]
    fn withdraw(&mut self, amt: u32);
}

#[ensures(resource(Money(), 10))]
fn client<B: Bank>(bank: &mut B) {
    bank.deposit(10);
    prusti_assert!(bank.balance() >= 10);
}

fn main() {

}
