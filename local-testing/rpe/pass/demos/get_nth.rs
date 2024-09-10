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

    #[requires(n < self.len())]
    fn get_nth(&mut self, n: usize) -> &mut u32 {
        if n == 0 {
            &mut self.head
        } else {
            match &mut self.tail {
                Some(ref mut tail) => tail.get_nth(n - 1),
                None => unreachable!(),
            }
        }
    }
}

fn main() {}
