use prusti_rustc_interface::{
    abi,
    ast::Mutability,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs, TyKind},
    },
    span::def_id::{DefId, LocalDefId},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{
    domain,
    lifted::{casters::CastTypePure, rust_ty_cast::RustTyCastersEnc},
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym_pure::PrustiSymValue,
};

use super::{EncodeSymValueResult, SymExprEncoder};

impl<'vir, 'sym, 'tcx> SymExprEncoder<'vir, 'sym, 'tcx> {
    pub fn encode_ref<T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        e: PrustiSymValue<'sym, 'tcx>,
        mutability: Mutability,
    ) -> EncodeSymValueResult<'vir, String> {
        let base = self.encode_sym_value(deps, e)?;
        let inner_ty = e.ty(self.vcx.tcx()).rust_ty();
        let cast = deps
            .require_local::<RustTyCastersEnc<CastTypePure>>(inner_ty)
            .unwrap();
        let base = cast.cast_to_generic_if_necessary(self.vcx, base);
        let ref_ty = self.vcx.tcx().mk_ty_from_kind(TyKind::Ref(
            self.vcx.tcx().lifetimes.re_erased,
            inner_ty,
            mutability,
        ));
        let ty = deps.require_local::<RustTySnapshotsEnc>(ref_ty).unwrap();
        if let domain::DomainEncSpecifics::StructLike(s) = ty.generic_snapshot.specifics {
            Ok(s.field_snaps_to_snap
                .apply(self.vcx, ty.ty_arg_exprs(self.vcx), vec![base]))
        } else {
            unreachable!()
        }
    }
}
