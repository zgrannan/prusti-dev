use crate::{ExprGen, ExprGenData, Type};

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdentifier<'a, Args>(pub &'a str, Args);

#[derive(Debug, Clone, Copy)]
pub struct BinaryArgs<'tcx>(Type<'tcx>, Type<'tcx>);
#[derive(Debug, Clone, Copy)]
pub struct NullaryArgs;

#[derive(Debug, Clone, Copy)]
pub struct UnaryArgs<'tcx>(pub Type<'tcx>);

#[derive(Debug, Clone, Copy)]
pub struct UnknownArgs<'tcx>(pub &'tcx[Type<'tcx>]);

impl<'a, T> FunctionIdentifier<'a, T> {
    pub const fn new(name: &'a str, args: T) -> Self {
        FunctionIdentifier(name, args)
    }
}

impl<'tcx> FunctionIdentifier<'tcx, UnknownArgs<'tcx>> {
    pub fn as_expr<Curr: 'tcx, Next: 'tcx>(
        &self,
        ctx: &'tcx crate::VirCtxt<'tcx>,
    ) -> ExprGen<'tcx, &'tcx [ExprGen<'tcx, Curr, Next>], ExprGen<'tcx, Curr, Next>> {
        ctx.alloc(ExprGenData::Lazy(
            self.0,
            Box::new(|vcx, args| {
                vcx.mk_func_app(self.0, args)
            }),
        ))
    }
}

impl<'tcx> FunctionIdentifier<'tcx, UnaryArgs<'tcx>> {
    pub fn as_expr<Curr: 'tcx, Next: 'tcx>(
        &self,
        ctx: &'tcx crate::VirCtxt<'tcx>,
    ) -> ExprGen<'tcx, ExprGen<'tcx, Curr, Next>, ExprGen<'tcx, Curr, Next>> {
        ctx.alloc(ExprGenData::Lazy(
            self.0,
            Box::new(|vcx, args| {
                vcx.mk_func_app(self.0, &[args])
            }),
        ))
    }
}

impl<'tcx> FunctionIdentifier<'tcx, BinaryArgs<'tcx>> {
    pub fn as_expr<Curr: 'tcx, Next: 'tcx>(
        &self,
        ctx: &'tcx crate::VirCtxt<'tcx>,
    ) -> ExprGen<
        'tcx,
        (ExprGen<'tcx, Curr, Next>, ExprGen<'tcx, Curr, Next>),
        ExprGen<'tcx, Curr, Next>,
    > {
        ctx.alloc(ExprGenData::Lazy(
            self.0,
            Box::new(|vcx, args| vcx.mk_func_app(self.0, &[args.0, args.1])),
        ))
    }
}

