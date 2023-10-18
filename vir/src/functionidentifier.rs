use std::marker::PhantomData;

use crate::{ExprGen, ExprGenData};
use crate::builtin_snapshot_constructor;

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdentifier<'tcx, ArgType>(pub &'tcx str, pub PhantomData<ArgType>);
struct Nullary;

#[derive(Debug, Clone, Copy)]
pub struct Unary;
struct Binary;

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


pub const BOOL_CONS: FunctionIdentifier<'static, Unary> = FunctionIdentifier(builtin_snapshot_constructor!("Bool"), PhantomData);