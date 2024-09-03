use middle::{
    mir::{interpret::Scalar, ConstValue},
    ty::VariantDiscr,
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
use symbolic_execution::{
    context::SymExContext,
    path_conditions::PathConditions,
    results::ResultPath,
    value::{Constant, SymValueData, Ty},
};

use std::{collections::BTreeSet, rc::Rc};
use task_encoder::{encoder_cache, TaskEncoder, TaskEncoderDependencies};
use vir::{add_debug_note, Reify};

use crate::{
    debug::visualization_data_dir,
    encoders::{
        mir_pure::PureKind,
        sym_pure::{PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult},
        CapabilityEnc, MirPureEnc, SymPureEnc,
    },
    sctx,
};
pub struct SymSpecEnc;

#[derive(Clone)]
pub struct SymSpec<'sym, 'tcx>(Vec<SymPureEncResult<'sym, 'tcx>>);

impl<'sym, 'tcx> SymSpec<'sym, 'tcx> {
    pub fn new() -> Self {
        Self(vec![])
    }
    pub fn singleton(value: SymPureEncResult<'sym, 'tcx>) -> Self {
        Self(vec![value])
    }

    pub fn into_iter(self) -> impl Iterator<Item = SymPureEncResult<'sym, 'tcx>> {
        self.0.into_iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = &SymPureEncResult<'sym, 'tcx>> {
        self.0.iter()
    }

    pub fn debug_ids(&self) -> BTreeSet<String> {
        self.0
            .iter()
            .flat_map(|value| value.debug_id.clone())
            .collect()
    }
}

#[derive(Clone)]
pub struct SymSpecEncOutput<'sym, 'tcx> {
    pub pres: SymSpec<'sym, 'tcx>,
    pub posts: SymSpec<'sym, 'tcx>,
    pub pledges: SymSpec<'sym, 'tcx>,
}

impl<'sym, 'tcx> SymSpecEncOutput<'sym, 'tcx> {
    pub fn debug_ids(&self) -> BTreeSet<String> {
        let mut debug_ids = self.pres.debug_ids();
        debug_ids.extend(self.posts.debug_ids());
        debug_ids.extend(self.pledges.debug_ids());
        debug_ids
    }
}

type SymSpecEncTask<'tcx> = (
    DefId,                    // The function annotated with specs
    ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    Option<DefId>,            // ID of the caller function, if any
);

pub fn mk_conj<'sym, 'tcx>(
    arena: &'sym SymExContext<'tcx>,
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

impl TaskEncoder for SymSpecEnc {
    encoder_cache!(SymSpecEnc);
    type TaskDescription<'vir> = SymSpecEncTask<'vir>;

    type OutputRef<'vir> = ()
        where Self: 'vir;

    type OutputFullLocal<'vir> = SymSpecEncOutput<'vir, 'vir>;

    type OutputFullDependency<'vir> = ()
        where Self: 'vir;

    type EnqueueingError = ();

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (def_id, substs, _caller_def_id) = task_key;

        let result = sctx::with_scx(|scx| {
            let panic_lang_items = [
                scx.tcx.lang_items().panic_fn().unwrap(),
                scx.tcx.lang_items().begin_panic_fn().unwrap(),
            ];

            if panic_lang_items.contains(&def_id) {
                return SymSpecEncOutput {
                    pres: Self::spec_bool(scx, false),
                    posts: SymSpec::new(),
                    pledges: SymSpec::new(),
                };
            }

            if scx.tcx.def_path_str(def_id) == "std::cmp::PartialEq::eq"
                || scx.tcx.def_path_str(def_id) == "std::cmp::PartialEq::ne"
            {
                // No spec necessary, will encode a function with a body
                return SymSpecEncOutput {
                    pres: SymSpec::new(),
                    posts: SymSpec::new(),
                    pledges: SymSpec::new(),
                };
            }

            let specs = deps
                .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask {
                    def_id: *def_id,
                })
                .unwrap();

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    SymPureEnc::encode(
                        scx,
                        crate::encoders::SymPureEncTask {
                            kind: PureKind::Spec,
                            parent_def_id: *spec_def_id,
                            param_env: scx.tcx.param_env(spec_def_id),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(*def_id),
                        },
                        visualization_data_dir(*spec_def_id, substs),
                    )
                })
                .collect::<Vec<_>>();

            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let post = SymPureEnc::encode(
                        scx,
                        crate::encoders::SymPureEncTask {
                            kind: PureKind::Spec,
                            parent_def_id: *spec_def_id,
                            param_env: scx.tcx.param_env(spec_def_id),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(*def_id),
                        },
                        visualization_data_dir(*spec_def_id, substs),
                    );
                    post
                })
                .collect::<Vec<_>>();

            let pledges = specs
                .pledges
                .iter()
                .map(|pledge| {
                    let post = SymPureEnc::encode(
                        scx,
                        crate::encoders::SymPureEncTask {
                            kind: PureKind::Spec,
                            parent_def_id: pledge.rhs,
                            param_env: scx.tcx.param_env(pledge.rhs),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(*def_id),
                        },
                        visualization_data_dir(pledge.rhs, substs),
                    );
                    post
                })
                .collect::<Vec<_>>();

            SymSpecEncOutput {
                pres: SymSpec(pres),
                posts: SymSpec(posts),
                pledges: SymSpec(pledges),
            }
        });
        Ok((result, ()))
    }
}

impl SymSpecEnc {
    pub fn spec_bool<'sym, 'tcx>(arena: &'sym SymExContext<'tcx>, b: bool) -> SymSpec<'sym, 'tcx> {
        let constant = arena.mk_constant(Constant::from_bool(arena.tcx, b));
        SymSpec::singleton(SymPureEncResult::from_sym_value(constant))
    }
}
