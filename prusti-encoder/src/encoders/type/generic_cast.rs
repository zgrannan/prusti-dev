use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, FunctionIdent, UnaryArity, UnknownArity};

use crate::encoders::{domain::DomainEnc, GenericEnc};

use super::{lifted::{LiftedTy, LiftedTyEnc}, most_generic_ty::MostGenericTy};

/// Takes as input the most generic version (c.f. `MostGenericTy`) of a Rust
/// type, and generates functions to convert the generic Viper representation of
/// a Rust expression with that type to its concrete representation, and
/// vice-versa. If the provided type is generic, it does nothing, returning
/// `GenericCastOutputRef::AlreadyGeneric`.
pub struct GenericCastEnc;

#[derive(Copy, Clone, Debug)]
pub enum GenericCastOutputRef<'vir> {
    CastFunctions {
        /// Casts a concrete type to a generic type
        make_generic: vir::FunctionIdent<'vir, UnknownArity<'vir>>,
        /// Casts a generic type to a concrete type
        make_concrete: vir::FunctionIdent<'vir, UnknownArity<'vir>>,
    },
    AlreadyGeneric,
}

impl<'vir> GenericCastOutputRef<'vir> {
    pub fn concrete_option(&self) -> Option<vir::FunctionIdent<'vir, UnknownArity<'vir>>> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => None,
            GenericCastOutputRef::CastFunctions { make_concrete, .. } => Some(*make_concrete),
        }
    }

    pub fn generic_option(&self) -> Option<vir::FunctionIdent<'vir, UnknownArity<'vir>>> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => None,
            GenericCastOutputRef::CastFunctions { make_generic, .. } => Some(*make_generic),
        }
    }

    /// Converts the snapshot `snap` to a generic "Param" snapshot, if it's not
    /// encoded as one already.
    pub fn cast_to_generic_if_necessary<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir>],
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => snap,
            GenericCastOutputRef::CastFunctions { make_generic, .. } => {
                let args = std::iter::once(snap)
                    .chain(ty_args.iter().map(|t| t.expr(vcx)))
                    .collect::<Vec<_>>();
                make_generic.apply(vcx, &args)
            }
        }
    }

    // Converts the snapshot `snap` to a concrete snapshot, if the concrete type
    // is known.
    pub fn cast_to_concrete_if_possible<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir>],
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => snap,
            GenericCastOutputRef::CastFunctions { make_concrete, .. } => {
                let args = std::iter::once(snap)
                    .chain(ty_args.iter().map(|t| t.expr(vcx)))
                    .collect::<Vec<_>>();
                make_concrete.apply(vcx, &args)
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
        vir::with_vcx(|vcx| {
            let domain_ref = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
            let ty_args = deps
                .require_local::<LiftedTyEnc>(ty.ty())
                .unwrap()
                .instantiation_arguments();
            let self_ty = domain_ref.domain.apply(vcx, []);
            let base_name = domain_ref.base_name;

            let mk_type_spec = |param| {
                let lifted_param_snap_ty = generic_ref.param_type_function.apply(vcx, [param]);
                vcx.mk_eq_expr(
                    lifted_param_snap_ty,
                    domain_ref.type_function.apply(
                        vcx,
                        ty_args
                            .iter()
                            .map(|t| vcx.mk_local_ex(t.name, t.ty))
                            .collect::<Vec<_>>()
                            .as_slice(),
                    ),
                )
            };

            let mut make_generic_arg_tys = vec![self_ty];
            let make_generic_arg_tys = std::iter::once(self_ty)
                .chain(ty_args.iter().map(|t| t.ty))
                .collect::<Vec<_>>();

            let make_generic_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "make_generic_s_{base_name}"),
                UnknownArity::new(vcx.alloc(make_generic_arg_tys)),
                generic_ref.param_snapshot,
            );

            let make_concrete_arg_tys = std::iter::once(generic_ref.param_snapshot)
                .chain(ty_args.iter().map(|t| t.ty))
                .collect::<Vec<_>>();

            let make_concrete_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "make_concrete_s_{base_name}"),
                UnknownArity::new(vcx.alloc(make_concrete_arg_tys)),
                self_ty,
            );

            deps.emit_output_ref::<Self>(
                *ty,
                GenericCastOutputRef::CastFunctions {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            );

            let make_generic_arg = vcx.mk_local_decl("self", self_ty);

            let make_generic_arg_decls = vcx.alloc_slice(
                &(std::iter::once(make_generic_arg)
                    .chain(ty_args.iter().map(|t| *t))
                    .collect::<Vec<_>>()),
            );

            let ty_arg_exprs = ty_args
                .iter()
                .map(|t| vcx.mk_local_ex(t.name, t.ty))
                .collect::<Vec<_>>();

            let make_generic_result = vcx.mk_local_ex("result", generic_ref.param_snapshot);

            let make_concrete_args = std::iter::once(make_generic_result)
                .chain(ty_arg_exprs.iter().map(|t| *t))
                .collect::<Vec<_>>();

            let make_generic_post = vcx.mk_eq_expr(
                make_concrete_ident.apply(vcx, &make_concrete_args),
                vcx.mk_local_ex(make_generic_arg.name, make_generic_arg.ty),
            );
            let make_generic = vcx.mk_function(
                make_generic_ident.name(),
                make_generic_arg_decls,
                generic_ref.param_snapshot,
                &[],
                vcx.alloc_slice(&[mk_type_spec(make_generic_result), make_generic_post]),
                None,
            );

            let make_concrete_arg_decl = vcx.mk_local_decl("snap", generic_ref.param_snapshot);
            let make_concrete_arg_decls = vcx.alloc_slice(
                &(std::iter::once(make_concrete_arg_decl)
                    .chain(ty_args.iter().map(|t| *t))
                    .collect::<Vec<_>>()),
            );

            let make_concrete_pre = mk_type_spec(
                vcx.mk_local_ex(make_concrete_arg_decl.name, make_concrete_arg_decl.ty),
            );

            let make_generic_args = std::iter::once(vcx.mk_local_ex("result", self_ty))
                .chain(ty_arg_exprs.iter().map(|t| *t))
                .collect::<Vec<_>>();

            let make_concrete_post = vcx.mk_eq_expr(
                make_generic_ident.apply(vcx, &make_generic_args),
                vcx.mk_local_ex(make_concrete_arg_decl.name, make_concrete_arg_decl.ty),
            );

            let make_concrete = vcx.mk_function(
                make_concrete_ident.name(),
                make_concrete_arg_decls,
                self_ty,
                vcx.alloc_slice(&[make_concrete_pre]),
                vcx.alloc_slice(&[make_concrete_post]),
                None,
            );

            Ok((vcx.alloc_slice(&[make_generic, make_concrete]), ()))
        })
    }
}
