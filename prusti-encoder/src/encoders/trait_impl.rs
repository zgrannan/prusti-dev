use prusti_rustc_interface::{hir::def_id::DefId, middle::ty::Ty};
use task_encoder::TaskEncoder;
use vir::vir_format_identifier;

use crate::encoders::lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc};

use super::TraitEnc;

pub struct TraitImplEnc;

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let ty = vcx.tcx().type_of(task_key).skip_binder();
            let trait_ref = vcx.tcx().impl_trait_ref(task_key).unwrap().skip_binder();
            let implements_fn = deps
                .require_ref::<TraitEnc>(trait_ref.def_id)?
                .implements_fn;
            let lifted_ty_expr = deps
                .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(ty)?
                .expr(vcx);
            let axiom = vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{}_implements_{}_axiom",
                    ty,
                    vcx.tcx().def_path_str(trait_ref.def_id)
                ),
                implements_fn.apply(vcx, [lifted_ty_expr]),
            );
            let domain = vcx.mk_domain(
                vir_format_identifier!(
                    vcx,
                    "{}_implements_{}_domain",
                    ty,
                    vcx.tcx().def_path_str(trait_ref.def_id)
                ),
                &[],
                vcx.alloc_slice(&[axiom]),
                &[],
            );
            Ok((domain, ()))
        })
    }
}
