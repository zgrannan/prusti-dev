use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, FunctionIdent, UnaryArity};

use crate::{
    encoders::{domain::DomainEnc, GenericEnc, SnapshotEnc},
    util::MostGenericTy,
};

pub struct GenericCastEnc;

#[derive(Copy, Clone, Debug)]
pub struct GenericCastOutputRef<'vir> {
    /// Casts a concrete type to a generic type
    pub make_generic: vir::FunctionIdent<'vir, UnaryArity<'vir>>,

    /// Casts a generic type to a concrete type
    pub make_concrete: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> task_encoder::OutputRefAny for GenericCastOutputRef<'vir> {}

#[derive(Clone)]
pub struct GenericCastOutput<'vir> {
    pub make_generic: vir::Function<'vir>,
    pub make_concrete: vir::Function<'vir>,
}

impl TaskEncoder for GenericCastEnc {
    task_encoder::encoder_cache!(GenericCastEnc);

    type TaskDescription<'vir> = MostGenericTy<'vir>;
    type OutputRef<'vir> = GenericCastOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericCastOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
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
        assert!(!ty.is_generic());
        vir::with_vcx(|vcx| {
            let domain_ref = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
            let self_ty = domain_ref.domain.apply(vcx, []);
            let base_name = domain_ref.base_name;
            let make_generic_arg_tys = vcx.alloc([self_ty]);
            let make_generic_arg_decls = vcx.alloc_slice(&[vcx.mk_local_decl("self", self_ty)]);

            let make_generic_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "make_generic_s_{base_name}"),
                UnaryArity::new(make_generic_arg_tys),
                generic_ref.param_snapshot,
            );

            let make_generic = vcx.mk_function(
                make_generic_ident.name(),
                make_generic_arg_decls,
                generic_ref.param_snapshot,
                &[],
                &[],
                None,
            );

            let make_concrete_arg_tys = vcx.alloc([generic_ref.param_snapshot]);
            let make_concrete_arg_decl = vcx.mk_local_decl("snap", generic_ref.param_snapshot);
            let make_concrete_arg_decls = vcx.alloc_slice(&[make_concrete_arg_decl]);

            let make_concrete_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "make_concrete_s_{base_name}"),
                UnaryArity::new(make_concrete_arg_tys),
                self_ty,
            );

            let domain_ref = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let num_ty_args = domain_ref.type_function.arity().len();
            let lifted_param_ty = generic_ref.param_type_function.apply(
                vcx,
                [vcx.mk_local_ex(make_concrete_arg_decl.name, make_concrete_arg_decl.ty)],
            );
            let make_concrete_pre = if num_ty_args > 0 {
                let typs = (0..num_ty_args).map(|i| {
                    vcx.mk_local_decl(vcx.alloc(format!("t{i}")), generic_ref.type_snapshot)
                });
                vcx.mk_exists_expr(
                    vcx.alloc_slice(typs.clone().collect::<Vec<_>>().as_slice()),
                    &[], // TODO
                    vcx.mk_eq_expr(
                        lifted_param_ty,
                        domain_ref.type_function.apply(
                            vcx,
                            typs.map(|t| vcx.mk_local_ex(t.name, t.ty))
                                .collect::<Vec<_>>()
                                .as_slice(),
                        ),
                    ),
                )
            } else {
                vcx.mk_eq_expr(lifted_param_ty, domain_ref.type_function.apply(vcx, &[]))
            };

            let make_concrete = vcx.mk_function(
                make_concrete_ident.name(),
                make_concrete_arg_decls,
                self_ty,
                vcx.alloc_slice(&[make_concrete_pre]),
                &[],
                None,
            );
            deps.emit_output_ref::<Self>(
                *ty,
                GenericCastOutputRef {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            );

            Ok((
                GenericCastOutput {
                    make_generic,
                    make_concrete,
                },
                (),
            ))
        })
    }
}
