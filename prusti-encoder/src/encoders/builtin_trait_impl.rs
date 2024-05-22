use prusti_rustc_interface::{hir::def_id::DefId, middle::ty::Ty};
use task_encoder::TaskEncoder;
use vir::vir_format_identifier;

use crate::encoders::lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc};

use super::TraitEnc;

pub struct BuiltinTraitImplEnc;

impl TaskEncoder for BuiltinTraitImplEnc {
    task_encoder::encoder_cache!(BuiltinTraitImplEnc);
    type TaskDescription<'tcx> = (
        Ty<'tcx>, // The type implementing the trait
        DefId,    // DefId of the trait
    );

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
        let trait_ref = deps.require_ref::<TraitEnc>(task_key.1)?;
        vir::with_vcx(|vcx| {
            let lifted_ty_expr = deps
                .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(task_key.0)?
                .expr(vcx);
            let axiom = vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{}_implements_{}_axiom",
                    task_key.0,
                    vcx.tcx().def_path_str(task_key.1)
                ),
                trait_ref.implements(lifted_ty_expr, &[]),
            );
            let domain = vcx.mk_domain(
                vir_format_identifier!(
                    vcx,
                    "{}_implements_{}_domain",
                    task_key.0,
                    vcx.tcx().def_path_str(task_key.1)
                ),
                &[],
                vcx.alloc_slice(&[axiom]),
                &[],
            );
            Ok((domain, ()))
        })
    }
}
