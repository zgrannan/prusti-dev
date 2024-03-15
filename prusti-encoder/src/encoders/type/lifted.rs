use prusti_rustc_interface::middle::ty::{self, ParamTy, TyKind};
use task_encoder::{OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{with_vcx, FunctionIdent, UnknownArity};

use crate::encoders::lifted_ty_function::LiftedTyFunctionEnc;

use super::{
    lifted_generic::{LiftedGeneric, LiftedGenericEnc},
    most_generic_ty::extract_type_params,
};

/// Representation of a Rust type as a Viper expression. The expression T
/// is used to represent a generic; this enables different encodings / substitutions
#[derive(Clone, Copy, Debug)]
pub enum LiftedTy<'vir, T> {
    /// Uninstantiated generic type parameter
    Generic(T),

    /// Non-generic type
    Instantiated {
        /// Type constructor function e.g. corresponding to `Option`, `Result`, etc
        ty_constructor: FunctionIdent<'vir, UnknownArity<'vir>>,

        /// Arguments to the type constructor e.g. `T` in `Option<T>`
        args: &'vir [LiftedTy<'vir, T>],
    },
}

impl<'vir, 'tcx, T: Copy> LiftedTy<'vir, T> {
    pub fn map<U: Copy>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        f: &mut dyn FnMut(T) -> U,
    ) -> LiftedTy<'vir, U> {
        match self {
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => {
                let args: Vec<LiftedTy<'vir, U>> = args.iter().map(|a| a.map(vcx, f)).collect::<Vec<_>>();
                LiftedTy::Instantiated {
                    ty_constructor: *ty_constructor,
                    args: vcx.alloc_slice(&args)
                }
            }
            LiftedTy::Generic(g) => LiftedTy::Generic(f(*g)),
        }
    }

    pub fn expect_instantiated(
        &self,
    ) -> (
        FunctionIdent<'vir, UnknownArity<'vir>>,
        &'vir [LiftedTy<'vir, T>],
    ) {
        match self {
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => (*ty_constructor, *args),
            _ => panic!("Expected instantiated type"),
        }
    }

    pub fn expect_generic(&self) -> T {
        match self {
            LiftedTy::Generic(g) => *g,
            _ => panic!("Expected generic type"),
        }
    }
}

impl<'vir, 'tcx> LiftedTy<'vir, ParamTy> {
    pub fn instantiate_with_lifted_generics(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies,
    ) -> LiftedTy<'vir, LiftedGeneric<'vir>> {
        self.map(vcx, &mut |g| deps.require_ref::<LiftedGenericEnc>(g).unwrap())
    }
}

impl<'vir, 'tcx, Curr, Next> LiftedTy<'vir, vir::ExprGen<'vir, Curr, Next>> {
    pub fn arg_exprs(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::ExprGen<'vir, Curr, Next>> {
        match self {
            LiftedTy::Generic(g) => vec![*g],
            LiftedTy::Instantiated { args, .. } => args.iter().map(|a| a.expr(vcx)).collect(),
        }
    }

    pub fn expr(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            LiftedTy::Generic(g) => *g,
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => ty_constructor.apply(vcx, &args.iter().map(|a| a.expr(vcx)).collect::<Vec<_>>()),
        }
    }
}

impl<'vir, 'tcx> LiftedTy<'vir, LiftedGeneric<'vir>> {
    /// Extracts the unique type parameters that should be used to instantiate
    /// the type, removing duplicate instances of the same parameter. For
    /// example, from type `Tuple3<T, U, Result<T, W>>` it would return `[T, U,
    /// W]`.
    ///
    /// This should only be necessary when encoding monomorphized versions of
    /// methods that may still contain generic types. In the future we will not
    /// be encoding monomorphised versions of methods, at that time this
    /// function can be removed.
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

    pub fn arg_exprs<Curr, Next>(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::ExprGen<'vir, Curr, Next>> {
        self.map(vcx, &mut |g| g.expr(vcx)).arg_exprs(vcx)
    }

    pub fn expr<Curr, Next>(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> vir::ExprGen<'vir, Curr, Next> {
        self.map(vcx, &mut |g| g.expr(vcx)).expr(vcx)
    }
}

impl<'vir> OutputRefAny for LiftedTy<'vir, ParamTy> {}
pub struct LiftedTyEnc;

impl TaskEncoder for LiftedTyEnc {
    task_encoder::encoder_cache!(LiftedTyEnc);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputFullLocal<'vir> = LiftedTy<'vir, ParamTy>;

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
        eprintln!("Encode LiftedTy {:?}", task_key.kind());
        deps.emit_output_ref::<Self>(*task_key, ());
        with_vcx(|vcx| {
            if let TyKind::Param(p) = task_key.kind() {
                return Ok((LiftedTy::Generic(*p), ()));
            }
            let (ty_constructor, args) = extract_type_params(vcx.tcx, *task_key);
            let ty_constructor = deps
                .require_ref::<LiftedTyFunctionEnc>(ty_constructor)
                .unwrap()
                .function;
            let args = args
                .into_iter()
                .map(|ty| deps.require_local::<Self>(ty).unwrap())
                .collect::<Vec<_>>();
            let result = LiftedTy::Instantiated {
                ty_constructor,
                args: vcx.alloc_slice(&args),
            };
            eprintln!("Output LiftedTy {:?}", task_key.kind());
            Ok((result, ()))
        })
    }
}
