#![feature(core_intrinsics, rustc_attrs)]
struct IntBox {
    val: i32
}

enum Expr {
    Sum(IntBox, IntBox),
    Constant(IntBox)
}

#[rustc_mir(borrowck_graphviz_postflow="log/analysis/unreachable-branch/compute.dot")]
fn compute(expr: Expr) -> i32 {
    let simplified = match expr {
        Expr::Sum(a, b) => Expr::Sum(b, a),
        x => x
    };

    let value = match simplified {
        Expr::Sum(_, _) => {
            unreachable!()  //~ ERROR unreachable!(..) statement might be reachable
        },
        Expr::Constant(IntBox { val }) => val
    };

    value
}

fn main() {}
