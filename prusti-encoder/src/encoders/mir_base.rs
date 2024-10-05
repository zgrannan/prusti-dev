#![allow(dead_code)]
#![allow(unused)]
use prusti_rustc_interface::{
    middle::{mir::{Local, LocalDecl}, ty},
};
use task_encoder::TaskEncoderDependencies;

use super::{rust_ty_snapshots::RustTySnapshotsEnc, SnapshotEnc, SymImpureEnc};

pub trait MirBaseEnc<'vir: 'enc, 'enc> {
    fn get_local_decl(&self, local: Local) -> &LocalDecl<'vir>;

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, SymImpureEnc>;

    fn get_ty_for_local(
        &mut self,
        local: Local
    ) -> vir::Type<'vir> {
        let ty = self.get_local_decl(local).ty;
        let deps = self.deps();
        if let ty::TyKind::Closure(..) = ty.kind() {
            // TODO: Support closure types
            &vir::TypeData::Unsupported(vir::UnsupportedType {
                name: "closure",
            })
        } else {
            deps.require_ref::<RustTySnapshotsEnc>(ty).unwrap().generic_snapshot.snapshot
        }
    }
}

