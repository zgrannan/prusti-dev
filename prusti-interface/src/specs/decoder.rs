use std::path::PathBuf;

use prusti_rustc_interface::{
    ast::AttrId,
    hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash},
    middle::{
        implement_ty_decoder,
        ty::{codec::TyDecoder, Ty, TyCtxt},
    },
    serialize::{opaque, Decodable},
    session::StableCrateId,
    span::{BytePos, ExpnId, Span, SpanDecoder, StableSourceFileId, Symbol, SyntaxContext},
};
use rustc_hash::FxHashMap;

pub struct DefSpecsDecoder<'a, 'tcx> {
    opaque: opaque::MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    ty_rcache: FxHashMap<usize, Ty<'tcx>>,
    specs_file: PathBuf,
    crate_name: String,
}

impl<'a, 'tcx> DefSpecsDecoder<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, data: &'a [u8], specs_file: PathBuf, crate_name: &str) -> Self {
        DefSpecsDecoder {
            opaque: opaque::MemDecoder::new(data, 0),
            tcx,
            ty_rcache: Default::default(),
            specs_file,
            crate_name: crate_name.to_string(),
        }
    }

    fn def_path_hash_to_def_id(&self, hash: DefPathHash) -> DefId {
        self.tcx
            .def_path_hash_to_def_id(hash, &"DefPathHash not found in the local crate")
        // // Sanity check let cstore = std::panic::AssertUnwindSafe(self.tcx.cstore_untracked());
        // let result = std::panic::catch_unwind(|| {
        //     cstore.stable_crate_id_to_crate_num(hash.stable_crate_id())
        // });
        // if result.is_err() {
        //     // The way to fix this in Prusti is to somehow regenerate the `.specs`
        //     // file whenever the DefPathHash might change (e.g. different args)
        //     let (specs_file, crate_name) = (&self.specs_file, &self.crate_name);
        //     let target_dir = specs_file.parent().unwrap();
        //     panic!(
        //         "A compiled dependency (referenced from `{specs_file:?}`) is out of sync. \
        //     Running `cargo clean -p {crate_name}` and rebuilding should fix this. \
        //     Otherwise try deleting the entire `{target_dir:?}` directory."
        //     )
        // }
        // // Get `DefId`
        // self.tcx
        //     .def_path_hash_to_def_id(hash, &"DefPathHash not found in the local crate")
    }
}

implement_ty_decoder!(DefSpecsDecoder<'a, 'tcx>);

impl<'a, 'tcx> SpanDecoder for DefSpecsDecoder<'a, 'tcx> {
    // See https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/decoder/struct.DecodeContext.html
    fn decode_span(&mut self) -> Span {
        let sm = self.tcx.sess.source_map();
        let pos = [(); 2].map(|_| {
            let ssfi = StableSourceFileId::decode(self);
            let rel_bp = BytePos::decode(self);
            sm.source_file_by_stable_id(ssfi)
                // See comment in 'encoder.rs'
                .map(|sf| sf.start_pos + rel_bp)
                // This should hopefully never fail,
                // so maybe could be an `unwrap` instead?
                .unwrap_or(BytePos(0))
        });
        Span::new(pos[0], pos[1], SyntaxContext::root(), None)
    }

    fn decode_symbol(&mut self) -> Symbol {
        todo!()
    }

    fn decode_expn_id(&mut self) -> ExpnId {
        todo!()
    }

    fn decode_syntax_context(&mut self) -> SyntaxContext {
        todo!()
    }

    fn decode_crate_num(&mut self) -> CrateNum {
        let stable_id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(stable_id)
    }

    // This impl makes sure that we get a runtime error when we try decode a
    // `DefIndex` that is not contained in a `DefId`. Such a case would be problematic
    // because we would not know how to transform the `DefIndex` to the current
    // context.
    fn decode_def_index(&mut self) -> DefIndex {
        panic!("trying to decode `DefIndex` outside the context of a `DefId`")
    }

    // Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
    // compilation sessions. We use the `DefPathHash`, which is stable across
    // sessions, to map the old `DefId` to the new one.
    fn decode_def_id(&mut self) -> DefId {
        let def_path_hash = DefPathHash::decode(self);
        self.def_path_hash_to_def_id(def_path_hash)
    }

    fn decode_attr_id(&mut self) -> AttrId {
        todo!()
    }
}

// impl<'a, 'tcx> TyDecoder for DefSpecsDecoder<'a, 'tcx> {
//     type I = TyCtxt<'tcx>;
//     const CLEAR_CROSS_CRATE: bool = true;

//     fn interner(&self) -> Self::I {
//         self.tcx
//     }

//     fn cached_ty_for_shorthand<F>(&mut self, shorthand: usize, or_insert_with: F) -> Ty<'tcx>
//     where
//         F: FnOnce(&mut Self) -> Ty<'tcx>,
//     {
//         if let Some(&ty) = self.ty_rcache.get(&shorthand) {
//             return ty;
//         }

//         let ty = or_insert_with(self);
//         self.ty_rcache.insert(shorthand, ty);
//         ty
//     }

//     fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
//     where
//         F: FnOnce(&mut Self) -> R,
//     {
//         let new_opaque = opaque::MemDecoder::new(self.opaque.data(), pos);
//         let old_opaque = std::mem::replace(&mut self.opaque, new_opaque);
//         let r = f(self);
//         self.opaque = old_opaque;
//         r
//     }

//     fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
//         unimplemented!("decode_alloc_id")
//     }
// }
