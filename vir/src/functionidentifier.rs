use std::marker::PhantomData;

use crate::{ExprGen, ExprGenData};

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdentifier<'a, ArgType>(pub &'a str, PhantomData<ArgType>);

impl <'a, T> FunctionIdentifier<'a, T> {
    pub const fn new(name: &'a str) -> Self {
        FunctionIdentifier(name, PhantomData)
    }
}
#[derive(Debug, Clone, Copy)]
pub struct Nullary;

impl Args for Nullary {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> = ();
    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
            _arg: ()
        ) -> Vec<ExprGen<'tcx, Curr, Next>> {
        vec![]
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Unary;
struct Binary;

#[derive(Debug, Clone, Copy)]
pub struct Unknown;

impl Args for Unary {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> = ExprGen<'tcx, Curr, Next> where Self: 'tcx;
    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
            arg: Self::ArgType<'tcx, Curr, Next>,
        ) -> Vec<ExprGen<'tcx, Curr, Next>> {
        vec![arg]
    }
}

impl Args for Unknown {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> = Vec<ExprGen<'tcx, Curr, Next>> where Self: 'tcx;
    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
            arg: Self::ArgType<'tcx, Curr, Next>,
        ) -> Vec<ExprGen<'tcx, Curr, Next>> { arg }
}

pub trait Args {
    type ArgType<'tcx, Curr: 'tcx, Next: 'tcx> where Self: 'tcx;

    fn to_vec<'tcx, Curr: 'tcx, Next: 'tcx>(
        arg: Self::ArgType<'tcx, Curr, Next>,
    ) -> Vec<ExprGen<'tcx, Curr, Next>>;
}