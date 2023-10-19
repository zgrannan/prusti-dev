use std::marker::PhantomData;

use crate::{ExprGen, ExprGenData};

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdentifier<'a, Args>(pub &'a str, PhantomData<Args>);

pub struct BinaryArgs;

impl <'a, T> FunctionIdentifier<'a, T> {
    pub const fn new(name: &'a str) -> Self {
        FunctionIdentifier(name, PhantomData)
    }
}

impl<'tcx> FunctionIdentifier<'tcx, UnknownArgs> {
    pub fn as_expr<Curr: 'tcx, Next: 'tcx>(&self, ctx: &'tcx crate::VirCtxt<'tcx>) -> 
        ExprGen<'tcx, &'tcx [ExprGen<'tcx, Curr, Next>], ExprGen<'tcx, Curr, Next>> {
        ctx.alloc(
            ExprGenData::Lazy(self.0, Box::new(|vcx, args| {
                vcx.mk_func_app(self.0, args)
            }))
        )
    }
}

impl<'tcx> FunctionIdentifier<'tcx, UnaryArgs> {
    pub fn as_expr<Curr: 'tcx, Next: 'tcx>(&self, ctx: &'tcx crate::VirCtxt<'tcx>) -> 
        ExprGen<'tcx, ExprGen<'tcx, Curr, Next>, ExprGen<'tcx, Curr, Next>> {
        ctx.alloc(
        ExprGenData::Lazy(self.0, Box::new(|vcx, args| {
            vcx.mk_func_app(self.0, &[args])
        }))
        )
    }
}

impl<'tcx> FunctionIdentifier<'tcx, BinaryArgs> {
    pub fn as_expr<Curr: 'tcx, Next: 'tcx>(&self, ctx: &'tcx crate::VirCtxt<'tcx>) -> 
        ExprGen<'tcx, (ExprGen<'tcx, Curr, Next>, ExprGen<'tcx, Curr, Next>), ExprGen<'tcx, Curr, Next>> {
        ctx.alloc(
        ExprGenData::Lazy(self.0, Box::new(|vcx, args| {
            vcx.mk_func_app(self.0, &[args.0, args.1])
        }))
        )
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

