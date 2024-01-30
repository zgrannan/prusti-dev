use prusti_rustc_interface::middle::ty::{self, TyKind};
use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{with_vcx, FunctionIdent, UnknownArity};

use crate::util::extract_type_params;

use super::{domain::DomainEnc, lifted_generic::{LiftedGeneric, LiftedGenericEnc}};

#[derive(Clone, Copy, Debug)]
pub enum LiftedTy<'vir> {
    Generic(LiftedGeneric<'vir>),
    Instantiated {
        ty_constructor: FunctionIdent<'vir, UnknownArity<'vir>>,
        args: &'vir [LiftedTy<'vir>],
    },
}

impl<'vir, 'tcx> LiftedTy<'vir> {
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

    type OutputRef<'vir> = LiftedTy<'vir>;

    type OutputFullLocal<'vir> = ();

    type OutputFullDependency<'vir> = ();

    type EnqueueingError = ();

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
        with_vcx(|vcx| {
            let output_ref = if let TyKind::Param(p) = task_key.kind() {
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
                    .map(|ty| deps.require_ref::<Self>(ty).unwrap())
                    .collect::<Vec<_>>();
                LiftedTy::Instantiated {
                    ty_constructor,
                    args: vcx.alloc_slice(&args),
                }
            };
            deps.emit_output_ref::<LiftedTyEnc>(*task_key, output_ref);
        });
        Ok(((), ()))
    }
}
