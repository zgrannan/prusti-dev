use prusti_rustc_interface::middle::ty;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, FunctionIdent, UnaryArity, VirCtxt};

use crate::{
    encoders::{domain::DomainEnc, GenericEnc},
    util::MostGenericTy,
};

pub struct GenericCastEnc;

#[derive(Copy, Clone, Debug)]
pub enum GenericCastOutputRef<'vir> {
    CastFunctions {
        /// Casts a concrete type to a generic type
        make_generic: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
        /// Casts a generic type to a concrete type
        make_concrete: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    },
    AlreadyGeneric,
}

impl<'vir> GenericCastOutputRef<'vir> {
    /// Converts the snapshot `snap` to a generic "Param" snapshot, if it's not
    /// encoded as one already.
    pub fn cast_to_generic_if_necessary<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => snap,
            GenericCastOutputRef::CastFunctions { make_generic, .. } => {
                make_generic.apply(vcx, [snap])
            }
        }
    }

    // Converts the snapshot `snap` to a concrete snapshot, if the concrete type
    // is known.
    pub fn cast_to_concrete_if_possible<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => snap,
            GenericCastOutputRef::CastFunctions { make_concrete, .. } => {
                make_concrete.apply(vcx, [snap])
            }
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for GenericCastOutputRef<'vir> {}

/// The list of cast functions, if any
type GenericCastOutput<'vir> = &'vir [vir::Function<'vir>];

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
        if ty.is_generic() {
            deps.emit_output_ref::<Self>(*ty, GenericCastOutputRef::AlreadyGeneric);
            return Ok((&[], ()));
        }
        assert!(!ty.is_generic());
        vir::with_vcx(|vcx| {
            let domain_ref = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
            let self_ty = domain_ref.domain.apply(vcx, []);
            let base_name = domain_ref.base_name;
            let make_generic_arg_tys = vcx.alloc([self_ty]);
            let make_generic_arg_decls = vcx.alloc_slice(&[vcx.mk_local_decl("self", self_ty)]);
            let num_ty_args = domain_ref.type_function.arity().len();

            let mk_type_spec = |param| {
                let lifted_param_snap_ty = generic_ref.param_type_function.apply(vcx, [param]);
                if num_ty_args > 0 {
                    let typs = (0..num_ty_args).map(|i| {
                        vcx.mk_local_decl(vcx.alloc(format!("t{i}")), generic_ref.type_snapshot)
                    });
                    vcx.mk_exists_expr(
                        vcx.alloc_slice(typs.clone().collect::<Vec<_>>().as_slice()),
                        &[], // TODO
                        vcx.mk_eq_expr(
                            lifted_param_snap_ty,
                            domain_ref.type_function.apply(
                                vcx,
                                typs.map(|t| vcx.mk_local_ex(t.name, t.ty))
                                    .collect::<Vec<_>>()
                                    .as_slice(),
                            ),
                        ),
                    )
                } else {
                    vcx.mk_eq_expr(
                        lifted_param_snap_ty,
                        domain_ref.type_function.apply(vcx, &[]),
                    )
                }
            };

            let make_generic_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "make_generic_s_{base_name}"),
                UnaryArity::new(make_generic_arg_tys),
                generic_ref.param_snapshot,
            );

            let make_generic_post =
                mk_type_spec(vcx.mk_local_ex("result", generic_ref.param_snapshot));

            let make_generic = vcx.mk_function(
                make_generic_ident.name(),
                make_generic_arg_decls,
                generic_ref.param_snapshot,
                &[],
                vcx.alloc_slice(&[make_generic_post]),
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

            let make_concrete_pre = mk_type_spec(
                vcx.mk_local_ex(make_concrete_arg_decl.name, make_concrete_arg_decl.ty),
            );

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
                GenericCastOutputRef::CastFunctions {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            );

            Ok((vcx.alloc_slice(&[make_generic, make_concrete]), ()))
        })
    }
}
