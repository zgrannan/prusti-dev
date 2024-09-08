use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::ty::{self, TypeFoldable},
};
use task_encoder::{
    EncodeFullError, TaskEncoder, TaskEncoderDependencies
};

/// TODO: doc
pub struct CapabilityEnc;

use super::predicate::{PredicateEnc, PredicateEncOutputRef};

impl TaskEncoder for CapabilityEnc {
    task_encoder::encoder_cache!(CapabilityEnc);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;
    type OutputRef<'vir> = PredicateEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        _deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), EncodeFullError<'vir, Self>> {
        vir::with_vcx(|_vcx| {
            // let mut folder = RegionRenumberVisitor {
            //     tcx: vcx.tcx(),
            //     map: FxHashMap::default(),
            // };
            // let ty = task_key.fold_with(&mut folder);
            // let mut out = deps.require_ref::<PredicateEnc>(ty).unwrap();
            // let inverse: FxHashMap<_, _> = folder.map.iter().map(|(k, v)| (*v, *k)).collect();
            // out.ref_to_region_refs = out.ref_to_region_refs.into_iter().map(|(v, d)| {
            //     // println!("backtranslate: {:?} -> {:?} ({d:?})", v, inverse[&v]);
            //     let v = inverse[&v];
            //     if v.is_var() {
            //         (v.as_var(), d)
            //     } else {
            //         (ty::RegionVid::MAX, d)
            //     }
            // }).collect();
            // deps.emit_output_ref::<Self>(*task_key, out);
            Ok(((), ()))
        })
    }
}

struct RegionRenumberVisitor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    map: FxHashMap<ty::Region<'tcx>, ty::RegionVid>,
}

// impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for RegionRenumberVisitor<'tcx> {
//     fn interner(&self) -> ty::TyCtxt<'tcx> {
//         self.tcx
//     }

//     fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
//         let len = self.map.len();
//         let v = *self.map.entry(r).or_insert_with(|| ty::RegionVid::from_usize(len));
//         ty::Region::new_var(self.tcx, v)
//     }
// }
