use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{ClauseKind, PredicateKind},
};
use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{vir_format_identifier, BinOpKind, CallableIdent, FunctionIdent, UnaryArity};

use super::GenericEnc;

pub struct TraitEnc;

#[derive(Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub implements_fn: FunctionIdent<'vir, UnaryArity<'vir>>,
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

            let generics = deps.require_ref::<GenericEnc>(())?;

            let implements_fn = FunctionIdent::new(
                vir_format_identifier!(vcx, "implements_{}", trait_name),
                UnaryArity::new(vcx.alloc([generics.type_snapshot])),
                &vir::TypeData::Bool,
            );

            deps.emit_output_ref(*task_key, TraitEncOutputRef { implements_fn })?;

            let mut axioms = vec![];

            let constraints = vcx.tcx().predicates_of(*task_key);

            let constraint_ty_decl = vcx.mk_local_decl("ty", generics.type_snapshot);
            let constraint_ty_expr =
                vcx.mk_local_ex(constraint_ty_decl.name, generics.type_snapshot);
            let axiom_qvars = vcx.alloc_slice(&[constraint_ty_decl]);
            let implements_this = implements_fn.apply(vcx, [constraint_ty_expr]);

            for (constraint, _) in constraints.predicates {
                match constraint.as_predicate().kind().skip_binder() {
                    PredicateKind::Clause(ClauseKind::Trait(trait_ref)) => {

                        if trait_ref.def_id() == *task_key {
                            continue;
                        }

                        let implements_other_fn =
                            deps.require_ref::<Self>(trait_ref.def_id())?.implements_fn;

                        let implements_other = implements_other_fn.apply(vcx, [constraint_ty_expr]);

                        let trigger = vcx.mk_trigger(vcx.alloc_slice(&[implements_other]));

                        let other_name = vcx.tcx().def_path_str(trait_ref.def_id());

                        eprintln!("{} implements {}", trait_name, other_name);

                        axioms.push(vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(
                                vcx,
                                "{}_implements_{}",
                                trait_name,
                                other_name,
                            ),
                            vcx.mk_forall_expr(
                                axiom_qvars,
                                vcx.alloc_slice(&[trigger]),
                                vcx.mk_bin_op_expr(
                                    BinOpKind::Implies,
                                    implements_this,
                                    implements_other
                                ),
                            ),
                        ))
                    }
                    _ => todo!(),
                }
            }

            let implements_fn = vcx.mk_domain_function(implements_fn, false);

            let domain = vcx.mk_domain(
                vir::vir_format_identifier!(vcx, "{}", trait_name),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&[implements_fn]),
            );
            Ok((domain, ()))
        })
    }
}
