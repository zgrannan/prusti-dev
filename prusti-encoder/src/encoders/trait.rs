use prusti_rustc_interface::
    hir::def_id::DefId
;
use rustc_middle::ty;
use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{
    vir_format_identifier, CallableIdent, FunctionIdent, UnknownArity,
};

use super::GenericEnc;

pub struct TraitEnc;

#[derive(Clone, Copy)]
pub struct TraitEncOutputRef<'vir> {
    implements_fn: FunctionIdent<'vir, UnknownArity<'vir>>,
}

impl<'vir> TraitEncOutputRef<'vir> {
    pub fn implements(
        &self,
        ty: vir::Expr<'vir>,
        trait_ty_args: &'vir [vir::Expr<'vir>],
    ) -> vir::Expr<'vir> {
        let args = std::iter::once(ty)
            .chain(trait_ty_args.iter().copied())
            .collect::<Vec<_>>();
        vir::with_vcx(|vcx| self.implements_fn.apply(vcx, &args))
    }
}

impl<'vir> OutputRefAny for TraitEncOutputRef<'vir> {}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    type TaskDescription<'vir> = DefId;

    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    type OutputRef<'vir> = TraitEncOutputRef<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let trait_name = vcx.tcx().def_path_str(*task_key);
            let trait_generics = vcx.tcx().generics_of(*task_key);
            let trait_ty_params = trait_generics
                .params
                .iter()
                .skip(1) // skip `Self`
                .filter_map(|param| {
                    if matches!(param.kind, ty::GenericParamDefKind::Type { .. }) {
                        Some(ty::ParamTy::for_def(param))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            let generics = deps.require_ref::<GenericEnc>(())?;

            let implements_fn = FunctionIdent::new(
                vir_format_identifier!(vcx, "implements_{}", trait_name),
                UnknownArity::new(
                    vcx.alloc_slice(&vec![generics.type_snapshot; trait_ty_params.len() + 1]),
                ),
                &vir::TypeData::Bool,
            );

            let output_ref = TraitEncOutputRef { implements_fn };
            deps.emit_output_ref(*task_key, output_ref)?;

            let implements_fn = vcx.mk_domain_function(implements_fn, false);

            let domain = vcx.mk_domain(
                vir::vir_format_identifier!(vcx, "{}", trait_name),
                &[],
                &[],
                vcx.alloc_slice(&[implements_fn]),
            );
            Ok((domain, ()))
        })
    }
}
