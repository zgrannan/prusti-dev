use prusti_contracts::*;

struct List {
    head: u32,
    tail: Option<Box<List>>,
}

#[pure]
#[trusted]
#[ensures(x < 1000)]
fn assume_small(x: usize) {}

impl List {
    #[pure]
    fn len(&self) -> usize {
        match self.tail {
            None => 1,
            Some(ref tail) => {
                assume_small(tail.len());
                1 + tail.len()
            }
        }
    }

    // #[pure]
    // #[requires(n < self.len())]
    // fn get_nth(&self, n: usize) -> u32 {
    //     if n == 0 {
    //         self.head
    //     } else {
    //         match &self.tail {
    //             Some(ref tail) => tail.get_nth(n - 1),
    //             None => unreachable!(),
    //         }
    //     }
    // }

    // #[requires(n < self.len())]
    // #[after_expiry(self.len() == old(self.len()) && self.get_nth(n) == before_expiry(*result))]
    // fn get_nth_mut(&mut self, n: usize) -> &mut u32 {
    //     let current = self;
    //     if n == 0 {
    //         &mut current.head
    //     } else {
    //         match &mut current.tail {
    //             Some(ref mut tail) => tail.get_nth_mut(n - 1),
    //             None => unreachable!(),
    //         }
    //     }
    // }

    // #[requires(n < self.len())]
    // #[after_expiry(self.len() == old(self.len()) && self.get_nth(n) == before_expiry(*result))]
    // fn get_nth_loop(&mut self, n: usize) -> &mut u32 {
    //     let mut i = 0;
    //     let mut current = self;
    //     while i < n {
    //         body_invariant!((n - i) < current.len());
    //         current = match current.tail {
    //             Some(ref mut tail) => tail,
    //             None => unreachable!(),
    //         };
    //         i += 1;
    //     }
    //     &mut current.head
    // }
}

fn main() {}
