use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies, TaskEncoderError};
use vir::{FunctionIdent, UnaryArity};

/// Takes a Rust `Ty` and returns a Viper `Type`. The returned type is always a
/// domain type. To get specifics such as constructors for the domain, use the
/// full encoding: this is generally the one to use as it also includes the type.
pub struct GenericSnapshotEnc;

#[derive(Clone, Debug)]
pub struct GenericSnapshotEncOutputRef<'vir> {
    pub snapshot: vir::Type<'vir>,
    pub cast_functions: Option<CastFunctions<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for GenericSnapshotEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct SnapshotEncOutput<'vir> {
    pub base_name: String,
    pub snapshot: vir::Type<'vir>,
    pub generics: &'vir [&'vir str],
    pub specifics: DomainEncSpecifics<'vir>,
    pub cast_functions: Option<CastFunctions<'vir>>,
}

use crate::util::{extract_type_params, to_placeholder, CastFunctions, MostGenericTy};

use super::domain::{DomainEnc, DomainEncSpecifics};

impl TaskEncoder for GenericSnapshotEnc {
    task_encoder::encoder_cache!(GenericSnapshotEnc);

    type TaskDescription<'tcx> = MostGenericTy<'tcx>;
    type OutputRef<'vir> = GenericSnapshotEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = SnapshotEncOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.with_normalized_param_name(vir::with_vcx(|vcx| vcx.tcx))
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        ty: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        vir::with_vcx(|vcx| {
            let out = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let snapshot = out.domain.apply(vcx, []);
            deps.emit_output_ref::<Self>(
                *ty,
                GenericSnapshotEncOutputRef {
                    snapshot,
                    cast_functions: out.cast_functions,
                },
            );
            let specifics = deps.require_dep::<DomainEnc>(*ty).unwrap();
            let generics = vcx.alloc_slice(
                ty.generics()
                    .iter()
                    .map(|g| match g.kind() {
                        TyKind::Param(param) => param.name.as_str(),
                        _ => unreachable!(),
                    })
                    .collect::<Vec<_>>()
                    .as_slice(),
            );
            Ok((
                SnapshotEncOutput {
                    base_name: out.base_name,
                    snapshot,
                    specifics,
                    generics,
                    cast_functions: out.cast_functions,
                },
                (),
            ))
        })
    }
}
