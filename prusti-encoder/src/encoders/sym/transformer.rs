use symbolic_execution::{
    context::SymExContext,
    transform::{BaseSymValueTransformer, SymValueTransformer},
};

use crate::encoders::sym_pure::{PrustiSymValSyntheticData, PrustiSymValue};
use prusti_rustc_interface::{
    ast,
    ast::Local,
    hir::{self, intravisit, Mutability},
    index::IndexVec,
    middle::{
        mir::{self, PlaceElem, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt, TyKind},
    },
    span::{def_id::DefId, symbol::Ident, Span},
    target::abi::FIRST_VARIANT,
};

#[allow(unused)]
trait PrustiSymValueTransformer<'sym, 'tcx: 'sym>:
    BaseSymValueTransformer<'sym, 'tcx, PrustiSymValSyntheticData<'sym, 'tcx>>
{
    fn transform_old(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        value: PrustiSymValue<'sym, 'tcx>,
    ) -> PrustiSymValue<'sym, 'tcx>;

    fn transform_pure_fn_call(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: &'sym [PrustiSymValue<'sym, 'tcx>],
    ) -> PrustiSymValue<'sym, 'tcx>;

    fn transform_synthetic(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        s: PrustiSymValSyntheticData<'sym, 'tcx>,
    ) -> PrustiSymValue<'sym, 'tcx> {
        match s {
            PrustiSymValSyntheticData::Old(value) => self.transform_old(arena, value),
            PrustiSymValSyntheticData::PureFnCall(def_id, substs, args) => {
                self.transform_pure_fn_call(arena, def_id, substs, args)
            }
            _ => todo!(),
        }
    }
}
