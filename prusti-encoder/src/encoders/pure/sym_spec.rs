use middle::{
    mir::interpret::{ConstValue, Scalar},
    ty::VariantDiscr,
};
use symbolic_execution::{
    path_conditions::PathConditions,
    value::{Constant, SymValueData, Ty},
    results::ResultPath, context::SymExContext,
};
use prusti_rustc_interface::{
    hir::lang_items,
    middle::{
        self,
        mir::{self, PlaceElem},
        ty::{self, VariantDef},
    },
    span::{def_id::DefId, DUMMY_SP},
};

use std::{collections::BTreeSet, rc::Rc};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{add_debug_note, Reify};

use crate::encoders::{
    mir_pure::PureKind,
    sym_pure::{PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult},
    CapabilityEnc, MirPureEnc, SymPureEnc,
};
pub struct SymSpecEnc;

#[derive(Clone)]
pub struct SymSpec<'sym, 'tcx>(BTreeSet<SymPureEncResult<'sym, 'tcx>>);

impl<'sym, 'tcx> SymSpec<'sym, 'tcx> {
    pub fn new() -> Self {
        Self(BTreeSet::new())
    }
    pub fn singleton(value: SymPureEncResult<'sym, 'tcx>) -> Self {
        Self(vec![value].into_iter().collect())
    }

    pub fn into_iter(self) -> impl Iterator<Item = SymPureEncResult<'sym, 'tcx>> {
        self.0.into_iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = &SymPureEncResult<'sym, 'tcx>> {
        self.0.iter()
    }
}

#[derive(Clone)]
pub struct SymSpecEncOutput<'sym, 'tcx> {
    pub pres: SymSpec<'sym, 'tcx>,
    pub posts: SymSpec<'sym, 'tcx>,
}
type SymSpecEncTask<'tcx> = (
    DefId,                    // The function annotated with specs
    ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    Option<DefId>,            // ID of the caller function, if any
);

pub fn mk_conj<'sym, 'tcx>(
    arena: &'sym SymExContext,
    tcx: ty::TyCtxt<'tcx>,
    sym_values: Vec<PrustiSymValue<'sym, 'tcx>>,
) -> PrustiSymValue<'sym, 'tcx> {
    let mut iter = sym_values.into_iter();
    if let Some(value) = iter.next() {
        iter.fold(value, |acc, val| {
            arena.mk_synthetic(arena.alloc(PrustiSymValSyntheticData::And(acc, val)))
        })
    } else {
        return arena.mk_constant(Constant::from_bool(tcx, true));
    }
}

impl SymSpecEnc {
    pub fn spec_bool<'sym, 'tcx>(
        arena: &'sym SymExContext,
        tcx: ty::TyCtxt<'tcx>,
        b: bool,
    ) -> SymSpec<'sym, 'tcx> {
        let constant = arena.mk_constant(Constant::from_bool(tcx, b));
        SymSpec::singleton(SymPureEncResult::from_sym_value(constant))
    }

    pub fn encode<'sym, 'tcx, 'vir, T: TaskEncoder>(
        arena: &'sym SymExContext,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        task_key: SymSpecEncTask<'tcx>,
    ) -> SymSpecEncOutput<'sym, 'tcx> {
        let (def_id, substs, caller_def_id) = task_key;

        vir::with_vcx(|vcx| {
            let panic_lang_items = [
                vcx.tcx().lang_items().panic_fn().unwrap(),
                vcx.tcx().lang_items().begin_panic_fn().unwrap(),
            ];

            if panic_lang_items.contains(&def_id) {
                return SymSpecEncOutput {
                    pres: Self::spec_bool(arena, vcx.tcx(), false),
                    posts: SymSpec::new(),
                };
            }

            if vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::eq"
                || vcx.tcx().def_path_str(def_id) == "std::cmp::PartialEq::ne"
            {
                // No spec necessary, will encode a function with a body
                return SymSpecEncOutput {
                    pres: SymSpec::new(),
                    posts: SymSpec::new(),
                };
            }

            let specs = deps
                .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })
                .unwrap();

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    SymPureEnc::encode(
                        arena,
                        crate::encoders::SymPureEncTask {
                            kind: PureKind::Spec,
                            parent_def_id: *spec_def_id,
                            param_env: vcx.tcx().param_env(spec_def_id),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(def_id),
                        },
                    )
                })
                .collect::<BTreeSet<_>>();

            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let post = SymPureEnc::encode(
                        arena,
                        crate::encoders::SymPureEncTask {
                            kind: PureKind::Spec,
                            parent_def_id: *spec_def_id,
                            param_env: vcx.tcx().param_env(spec_def_id),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(def_id),
                        },
                    );
                    post
                })
                .collect::<BTreeSet<_>>();
            SymSpecEncOutput {
                pres: SymSpec(pres),
                posts: SymSpec(posts),
            }
        })
    }
}
