use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, FunctionIdent, UnaryArity, UnknownArity};

use crate::encoders::{domain::DomainEnc, lifted_ty_function::LiftedTyFunctionEnc, GenericEnc};

use super::{
    lifted::{LiftedTy, LiftedTyEnc},
    lifted_generic::LiftedGeneric,
    most_generic_ty::MostGenericTy,
};

pub type MakeGenericCastFunction<'vir> = FunctionIdent<'vir, UnaryArity<'vir>>;

/// Takes as input the most generic version (c.f. `MostGenericTy`) of a Rust
/// type, and generates functions to convert the generic Viper representation of
/// a Rust expression with that type to its concrete representation, and
/// vice-versa. If the provided type is generic, it does nothing, returning
/// `GenericCastOutputRef::AlreadyGeneric`.
pub struct GenericCastEnc;

#[derive(Copy, Clone, Debug)]
pub enum GenericCastOutputRef<'vir> {
    CastFunctions {
        /// Casts a concrete expression to a generic expression (s_Param). The first
        /// argument is the snapshot encoding of the expression. Remaining
        /// arguments are type parameters.
        make_generic: MakeGenericCastFunction<'vir>,
        /// Casts a generic expression to a concrete expression. The first
        /// argument is the snapshot encoding of the expresion (an s_Param).
        /// Remaining arguments are type parameters.
        make_concrete: vir::FunctionIdent<'vir, UnknownArity<'vir>>,
    },
    AlreadyGeneric,
}

impl<'vir> GenericCastOutputRef<'vir> {
    /// Returns the function that casts the concrete expression to a generic
    /// expression (s_Param), if the input type wasn't already a generic
    /// expression.
    pub fn generic_option(&self) -> Option<MakeGenericCastFunction<'vir>> {
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
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            GenericCastOutputRef::AlreadyGeneric => snap,
            GenericCastOutputRef::CastFunctions { make_generic, .. } => {
                make_generic.apply(vcx, [snap])
            }
        }
    }

    /// Converts the snapshot `snap` to a concrete snapshot, if the concrete type
    /// is known.
    pub fn cast_to_concrete_if_possible<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
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
        eprintln!("Encode GenericCast {:?}", ty.kind());
        if ty.is_generic() {
            deps.emit_output_ref::<Self>(*ty, GenericCastOutputRef::AlreadyGeneric);
            return Ok((&[], ()));
        }
        vir::with_vcx(|vcx| {
            let domain_ref = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
            let lifted_ty = deps.require_local::<LiftedTyEnc>(ty.ty()).unwrap();
            let self_ty = domain_ref.domain.apply(vcx, []);
            let base_name = domain_ref.base_name;
            let type_function = deps
                .require_ref::<LiftedTyFunctionEnc>(*ty)
                .unwrap()
                .function;

            let mk_type_spec = |param, args| {
                let lifted_param_snap_ty = generic_ref.param_type_function.apply(vcx, [param]);
                vcx.mk_eq_expr(lifted_param_snap_ty, type_function.apply(vcx, args))
            };

            let make_generic_arg_tys = [self_ty];
            let make_generic_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "make_generic_s_{base_name}"),
                UnaryArity::new(vcx.alloc(make_generic_arg_tys)),
                generic_ref.param_snapshot,
            );

            let make_concrete_generics = lifted_ty
                .instantiate_with_lifted_generics(vcx, deps)
                .expect_instantiated()
                .1
                .iter()
                .map(|t| t.expect_generic())
                .collect::<Vec<_>>();

            let make_concrete_arg_tys = std::iter::once(generic_ref.param_snapshot)
                .chain(make_concrete_generics.iter().map(|t| t.ty()))
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
            eprintln!("Output GenericCast Ref {:?}", ty.kind());

            let make_generic_arg = vcx.mk_local_decl("self", self_ty);
            let make_generic_expr = vcx.mk_local_ex(make_generic_arg.name, make_generic_arg.ty);

            let make_generic_arg_decls = vcx.alloc_slice(&[make_generic_arg]);

            let make_concrete_ty_arg_exprs = make_concrete_generics
                .iter()
                .map(|t| t.expr(vcx))
                .collect::<Vec<_>>();

            let make_generic_result = vcx.mk_local_ex("result", generic_ref.param_snapshot);

            let ty_params_from_snap = lifted_ty
                .expect_instantiated()
                .1
                .iter()
                .zip(domain_ref.generic_accessors.iter())
                .map(|(_, accessor)| accessor.apply(vcx, [make_generic_expr]))
                .collect::<Vec<_>>();

            let make_generic = vcx.mk_function(
                make_generic_ident.name(),
                make_generic_arg_decls,
                generic_ref.param_snapshot,
                &[],
                vcx.alloc_slice(&[
                    mk_type_spec(make_generic_result, &ty_params_from_snap),
                    vcx.mk_eq_expr(
                        make_concrete_ident.apply(
                            vcx,
                            &std::iter::once(make_generic_result)
                                .chain(ty_params_from_snap.iter().map(|t| *t))
                                .collect::<Vec<_>>(),
                        ),
                        make_generic_expr,
                    ),
                ]),
                None,
            );

            let make_concrete_arg_decl = vcx.mk_local_decl("snap", generic_ref.param_snapshot);
            let make_concrete_arg_decls = vcx.alloc_slice(
                &std::iter::once(make_concrete_arg_decl)
                    .chain(make_concrete_generics.iter().map(|t| t.decl()))
                    .collect::<Vec<_>>(),
            );

            let make_concrete_pre = mk_type_spec(
                vcx.mk_local_ex(make_concrete_arg_decl.name, make_concrete_arg_decl.ty),
                &make_concrete_ty_arg_exprs,
            );

            let make_generic_args = [vcx.mk_local_ex("result", self_ty)];

            let make_concrete_post = vcx.mk_eq_expr(
                make_generic_ident.apply(vcx, make_generic_args),
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
