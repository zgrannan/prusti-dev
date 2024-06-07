use prusti_contracts::*;

struct Tuple2<T1, T2>(T1, T2);

struct Wrapper<T>(T);

#[pure]
fn insideWrapper<U>(u: Wrapper<U>) -> U { u.0 }

#[pure]
fn tupleInsideWrapper<U, V>(u: Wrapper<Tuple2<U, V>>) -> Tuple2<U, V> { insideWrapper(u) }


#[ensures(tupleInsideWrapper(Wrapper(Tuple2(7, 1))).0 == insideWrapper(Wrapper(7)))]
fn main() {

}
