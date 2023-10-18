use std::marker::PhantomData;

use crate::ExprGen;

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdentifier<'a, Args>(pub &'a str, PhantomData<Args>);

impl<'a, Args> FunctionIdentifier<'a, Args> {
    pub const fn new(name: &'a str) -> Self {
        FunctionIdentifier(name, PhantomData)
    }
}
pub trait Args {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx>
    where
        Self: 'tcx;

    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
        arg: Self::ArgType<'tcx, Curr, Next>,
    ) -> Vec<ExprGen<'tcx, Curr, Next>>;
}

#[derive(Debug, Clone, Copy)]
pub struct NullaryArgs;

impl Args for NullaryArgs {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> = ();
    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(_arg: ()) -> Vec<ExprGen<'tcx, Curr, Next>> {
        vec![]
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UnaryArgs;

impl Args for UnaryArgs {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> = ExprGen<'tcx, Curr, Next> where Self: 'tcx;
    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
        arg: Self::ArgType<'tcx, Curr, Next>,
    ) -> Vec<ExprGen<'tcx, Curr, Next>> {
        vec![arg]
    }
}
#[derive(Debug, Clone, Copy)]
pub struct UnknownArgs;

impl Args for UnknownArgs {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> = Vec<ExprGen<'tcx, Curr, Next>> where Self: 'tcx;
    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
        arg: Self::ArgType<'tcx, Curr, Next>,
    ) -> Vec<ExprGen<'tcx, Curr, Next>> {
        arg
    }
}

