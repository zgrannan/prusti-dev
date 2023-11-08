#![allow(dead_code)]
use prusti_contracts::*;

#[resource_kind]
struct Money(u32);

#[invariant_twostate(
    holds(Money(self.id())) - old(holds(Money(self.id()))) ==
    PermAmount::from(self.balance() - old(self.balance()))
)]
#[invariant_twostate(self.id() == old(self.id()))]
#[invariant(PermAmount::from(self.balance()) >= holds(Money(self.id())))]
trait Bank {

    #[pure]
    fn id(&self) -> u32;

    #[pure]
    fn balance(&self) -> u64;

    #[ensures(resource(Money(self.id()), amt))]
    fn deposit(&mut self, amt: u64);

    #[requires(resource(Money(self.id()), amt))]
    fn withdraw(&mut self, amt: u64);
}

#[ensures(resource(Money(bank.id()), 10))]
fn client<B: Bank>(bank: &mut B) {
    bank.deposit(10);
    // prusti_assert!(bank.id() == old(bank.id()));  
    // prusti_assert!(bank.balance() >= 10);
    // prusti_assert!(bank.id() > 5);
}

#[requires(bank1.id() != bank2.id())]
#[ensures(resource(Money(bank2.id()), 10))]
fn client2<B: Bank>(bank1: &mut B, bank2: &mut B) {
    bank2.deposit(10);
    // prusti_assert!(bank2.balance() >= 10);
}

#[ensures(resource(Money(bank.id()), 20))]
fn client3<B: Bank>(bank: &mut B) {
    client(bank);
    client(bank);
}


fn main() {

}
