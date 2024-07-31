use std::{cell::RefCell, fmt::Debug};

use symbolic_execution::context::SymExContext;

thread_local! {
    static SCTX: RefCell<Option<SymExContext<'static>>> = RefCell::new(None);
}

pub fn init_scx<'tcx>(scx: SymExContext<'tcx>) {
    SCTX.replace(Some(unsafe { std::mem::transmute(scx) }));
}

/// Perform an action with the sym context.
pub fn with_scx<'sym, 'tcx: 'sym, F, R>(f: F) -> R
where
    F: FnOnce(&'sym SymExContext<'tcx>) -> R,
{
    SCTX.with_borrow(|scx: &Option<SymExContext<'static>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let scx = scx.as_ref().expect("VIR context was not initialised");
        let scx = unsafe { std::mem::transmute(scx) };
        f(scx)
    })
}
