use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxIndexSet},
    hir::def_id::{CrateNum, DefId, DefIndex},
    middle::{
        mir::interpret::AllocId,
        ty::{self, codec::TyEncoder, PredicateKind, Ty, TyCtxt},
    },
    serialize::{opaque, Encodable, Encoder},
    span::{ExpnId, Span, SpanEncoder, StableSourceFileId, Symbol, SyntaxContext},
};

pub struct DefSpecsEncoder<'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<PredicateKind<'tcx>, usize>,
    interpret_allocs: FxIndexSet<AllocId>,
}

impl<'tcx> DefSpecsEncoder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, path: &std::path::PathBuf) -> std::io::Result<Self> {
        Ok(DefSpecsEncoder {
            tcx,
            opaque: opaque::FileEncoder::new(path)?,
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
            interpret_allocs: Default::default(),
        })
    }

    pub fn finish(mut self) -> Result<usize, std::io::Error> {
        self.opaque.finish().map_err(|(_, e)| e)
    }
}

// Taken from rustc:
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/encoder/macro.encoder_methods.html
macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) -> () {
            self.opaque.$name(value)
        })*
    }
}
impl<'tcx> Encoder for DefSpecsEncoder<'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);

        emit_raw_bytes(&[u8]);
    }
}

// impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for DefId {
//     fn encode(&self, s: &mut DefSpecsEncoder<'tcx>) {
//         s.tcx.def_path_hash(*self).encode(s)
//     }
// }

// impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for DefIndex {
//     fn encode(&self, _: &mut DefSpecsEncoder<'tcx>) {
//         panic!("encoding `DefIndex` without context");
//     }
// }

// impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for CrateNum {
//     fn encode(&self, s: &mut DefSpecsEncoder<'tcx>) {
//         s.tcx.stable_crate_id(*self).encode(s)
//     }
// }

// See https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/encoder/struct.EncodeContext.html
// impl<'tcx> Encodable<DefSpecsEncoder<'tcx>> for Span {
//     fn encode(&self, s: &mut DefSpecsEncoder<'tcx>) {
//         let sm = s.tcx.sess.source_map();
//         for bp in [self.lo(), self.hi()] {
//             let sf = sm.lookup_source_file(bp);
//             let ssfi = StableSourceFileId::new(&sf);
//             ssfi.encode(s);
//             // Not sure if this is the most stable way to encode a BytePos. If it fails
//             // try finding a function in `SourceMap` or `SourceFile` instead. E.g. the
//             // `bytepos_to_file_charpos` fn which returns `CharPos` (though there is
//             // currently no fn mapping back to `BytePos` for decode)
//             (bp - sf.start_pos).encode(s);
//         }
//     }
// }

impl<'tcx> SpanEncoder for DefSpecsEncoder<'tcx> {
    // See https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/encoder/struct.EncodeContext.html
    fn encode_span(&mut self, span: Span) {
        let sm = self.tcx.sess.source_map();
        for bp in [span.lo(), span.hi()] {
            let sf = sm.lookup_source_file(bp);
            let ssfi = sf.stable_id; //StableSourceFileId::new(&sf);
            ssfi.encode(self);
            // Not sure if this is the most stable way to encode a BytePos. If it fails
            // try finding a function in `SourceMap` or `SourceFile` instead. E.g. the
            // `bytepos_to_file_charpos` fn which returns `CharPos` (though there is
            // currently no fn mapping back to `BytePos` for decode)
            (bp - sf.start_pos).encode(self);
        }
    }

    fn encode_symbol(&mut self, symbol: Symbol) {
        todo!()
    }

    fn encode_expn_id(&mut self, expn_id: ExpnId) {
        todo!()
    }

    fn encode_syntax_context(&mut self, syntax_context: SyntaxContext) {
        todo!()
    }

    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        self.tcx.stable_crate_id(crate_num).encode(self)
    }

    fn encode_def_index(&mut self, def_index: DefIndex) {
        todo!()
    }

    fn encode_def_id(&mut self, def_id: DefId) {
        self.tcx.def_path_hash(def_id).encode(self)
    }
}

impl<'tcx> TyEncoder for DefSpecsEncoder<'tcx> {
    type I = TyCtxt<'tcx>;
    const CLEAR_CROSS_CRATE: bool = true;

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &rustc_middle::mir::interpret::AllocId) {
        let (index, _) = self.interpret_allocs.insert_full(*alloc_id);

        index.encode(self)
    }
}
