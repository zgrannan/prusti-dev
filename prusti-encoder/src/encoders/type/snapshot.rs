use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies, TaskEncoderError,
};

/// Takes a Rust `Ty` and returns a Viper `Type`. The returned type is always a
/// domain type. To get specifics such as constructors for the domain, use the
/// full encoding: this is generally the one to use as it also includes the type.
pub struct SnapshotEnc;

#[derive(Clone, Debug)]
pub struct SnapshotEncOutputRef<'vir> {
    pub snapshot: vir::Type<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for SnapshotEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct SnapshotEncOutput<'vir> {
    pub base_name: String,
    pub snapshot: vir::Type<'vir>,
    pub generics: &'vir [&'vir str],
    pub specifics: DomainEncSpecifics<'vir>,
}

use crate::util::{to_placeholder, MostGenericTy, extract_type_params};

use super::domain::{DomainEnc, DomainEncSpecifics};

impl TaskEncoder for SnapshotEnc {
    task_encoder::encoder_cache!(SnapshotEnc);

    type TaskDescription<'tcx> = MostGenericTy<'tcx>;
    type OutputRef<'vir> = SnapshotEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = SnapshotEncOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        ty: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        vir::with_vcx(|vcx| {

            // Generics shouldn't be encoded here, because the snapshot encoder returns a vir::Type
            // Generics are encoded as expressions (i.e. with type `s_Param`)
            assert!(!matches!(ty.kind(), TyKind::Param(_)));

            let out = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let snapshot = out.domain.apply(vcx, []);
            deps.emit_output_ref::<Self>(*ty, SnapshotEncOutputRef { snapshot });
            let specifics = deps.require_dep::<DomainEnc>(*ty).unwrap();
            let generics = vcx.alloc_slice(ty.generics().iter()
                .map(|g| match g.kind() {
                    TyKind::Param(param) => param.name.as_str(),
                    _ => unreachable!(),

                }).collect::<Vec<_>>().as_slice());
            Ok((SnapshotEncOutput { base_name: out.base_name, snapshot, specifics, generics }, ()))
        })
    }
}

impl SnapshotEnc {
    pub fn require_local<'tcx: 'vir, 'vir>(
        ty: ty::Ty<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<SnapshotEncOutput<'vir>, TaskEncoderError<SnapshotEnc>> {
        vir::with_vcx( |vcx| {
        let (ty, args) = extract_type_params(vcx.tcx, ty);
        for arg in args {
            if matches!(arg.kind(), TyKind::Param(_)) {
                continue;
            }
            Self::require_local(arg, deps)?;
        }
        deps.require_local::<Self>(ty)
        })
    }
}