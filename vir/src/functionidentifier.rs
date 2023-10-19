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

#[derive(Debug, Clone, Copy)]
pub struct NullaryArgs;

#[derive(Debug, Clone, Copy)]
pub struct UnaryArgs;

#[derive(Debug, Clone, Copy)]
pub struct UnknownArgs;