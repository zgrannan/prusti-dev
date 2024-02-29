use prusti_rustc_interface::middle::ty::{self, TyKind};
use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{with_vcx, FunctionIdent, UnknownArity};

use super::{domain::DomainEnc, lifted_generic::{LiftedGeneric, LiftedGenericEnc}, most_generic_ty::extract_type_params};

/// Representation of a Rust type as a Viper expression
#[derive(Clone, Copy, Debug)]
pub enum LiftedTy<'vir> {
    /// Uninstantiated generic type parameter
    Generic(LiftedGeneric<'vir>),
    /// Non-generic type
    Instantiated {
        /// Type constructor function e.g. corresponding to `Option`, `Result`, etc
        ty_constructor: FunctionIdent<'vir, UnknownArity<'vir>>,

        /// Arguments to the type constructor e.g. `T` in `Option<T>`
        args: &'vir [LiftedTy<'vir>],
    },
}

impl<'vir, 'tcx> LiftedTy<'vir> {
    /// Extracts the unique type parameters that should be used to instantiate
    /// the type, removing duplicate instances of the same parameter. For
    /// example, from type `Tuple3<T, U, Result<T, W>>` it would return `[T, U,
    /// W]`.
    pub fn instantiation_arguments(&self) -> Vec<vir::LocalDecl<'vir>> {
        match self {
            LiftedTy::Generic(g) => vec![g.decl()],
            LiftedTy::Instantiated { args, .. } => {
                let mut buf = vec![];
                for arg in args.iter() {
                    for ia in arg.instantiation_arguments() {
                        if !buf.contains(&ia) {
                            buf.push(ia);
                        }
                    }
                }
                buf
            }
        }
    }

    pub fn arg_exprs(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::Expr<'vir>> {
        match self {
            LiftedTy::Generic(g) => vec![g.expr(vcx)],
            LiftedTy::Instantiated { args, .. } => {
                args.iter().map(|a| a.expr(vcx)).collect::<Vec<_>>()
            }
        }
    }

    pub fn expr(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> vir::Expr<'vir> {
        match self {
            LiftedTy::Generic(g) => g.expr(vcx),
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => ty_constructor.apply(vcx, &args.iter().map(|a| a.expr(vcx)).collect::<Vec<_>>()),
        }
    }
}

impl<'vir> OutputRefAny for LiftedTy<'vir> {}

pub struct LiftedTyEnc;

impl TaskEncoder for LiftedTyEnc {
    task_encoder::encoder_cache!(LiftedTyEnc);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputFullLocal<'vir> = LiftedTy<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir>,
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
        deps.emit_output_ref::<Self>(*task_key, ());
        with_vcx(|vcx| {
            let result = if let TyKind::Param(p) = task_key.kind() {
                LiftedTy::Generic(
                    deps.require_ref::<LiftedGenericEnc>(p).unwrap()
                )
            } else {
                let (generic_ty, args) = extract_type_params(vcx.tcx, *task_key);
                let ty_constructor = deps
                    .require_ref::<DomainEnc>(generic_ty)
                    .unwrap()
                    .type_function;
                let args = args
                    .into_iter()
                    .map(|ty| deps.require_local::<Self>(ty).unwrap())
                    .collect::<Vec<_>>();
                LiftedTy::Instantiated {
                    ty_constructor,
                    args: vcx.alloc_slice(&args),
                }
            };
            Ok((result, ()))
        })
    }
}
