use crate::{ExprGen, Type};

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdentifier<'a, Args>(pub &'a str, Args);

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
    pub fn apply<Curr: 'tcx, Next: 'tcx>(
        &self,
        vcx: &'tcx crate::VirCtxt<'tcx>,
        args: &'tcx [ExprGen<'tcx, Curr, Next>]
    ) -> ExprGen<'tcx, Curr, Next>{
        vcx.mk_func_app(self.0, args)
    }
}

impl<'tcx> FunctionIdentifier<'tcx, UnaryArgs<'tcx>> {
    pub fn apply<Curr: 'tcx, Next: 'tcx>(
        &self,
        vcx: &'tcx crate::VirCtxt<'tcx>,
        args: ExprGen<'tcx, Curr, Next>
    ) -> ExprGen<'tcx, Curr, Next>{
        vcx.mk_func_app(self.0, &[args])
    }

}