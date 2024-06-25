use prusti_rustc_interface::{
    abi,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use task_encoder::TaskEncoder;

use crate::encoders::{
    domain,
    lifted::{casters::CastTypePure, rust_ty_cast::RustTyCastersEnc},
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym_pure::PrustiSymValue,
};

use super::{EncodeSymValueResult, SymExprEncoder};

impl<'enc, 'vir, 'sym, 'tcx, T: TaskEncoder> SymExprEncoder<'enc, 'vir, 'sym, 'tcx, T> {
    pub fn encode_ref(
        &mut self,
        ty: ty::Ty<'tcx>,
        e: PrustiSymValue<'sym, 'tcx>,
    ) -> EncodeSymValueResult<'vir> {
        let base = self.encode_sym_value(e).unwrap();
        let cast = self
            .deps
            .require_local::<RustTyCastersEnc<CastTypePure>>(e.ty(self.vcx.tcx()).rust_ty())
            .unwrap();
        let base = cast.cast_to_generic_if_necessary(self.vcx, base);
        let ty = self.deps.require_local::<RustTySnapshotsEnc>(ty).unwrap();
        if let domain::DomainEncSpecifics::StructLike(s) = ty.generic_snapshot.specifics {
            Ok(s.field_snaps_to_snap
                .apply(self.vcx, self.vcx.alloc(&vec![base])))
        } else {
            unreachable!()
        }
    }
}
