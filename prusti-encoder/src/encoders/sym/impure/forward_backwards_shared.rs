use std::{
    collections::{hash_map::DefaultHasher, BTreeMap},
    marker::PhantomData,
};

use pcs::combined_pcs::BodyWithBorrowckFacts;
use prusti_rustc_interface::{
    abi,
    hir::Mutability,
    index::IndexVec,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, Local, LocalDecl, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use std::hash::{Hash, Hasher};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    results::{ResultPath, SymbolicExecutionResult},
    value::{Substs, SymValueData, SymValueKind},
    Assertion,
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, CallableIdent, MethodIdent, UnknownArity};

#[derive(Clone, Debug)]
pub enum MirImpureEncError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
    pub backwards_fns: BTreeMap<usize, vir::FunctionIdent<'vir, UnknownArity<'vir>>>,
}
impl<'vir> task_encoder::OutputRefAny for MirImpureEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutput<'vir> {
    pub fn_debug_name: String,
    pub method: vir::Method<'vir>,
    pub backwards_method: vir::Method<'vir>,
    pub backwards_fns_domain: vir::Domain<'vir>,
}

use crate::{
    encoder_traits::pure_function_enc::mk_type_assertion,
    encoders::{
        lifted::{cast::CastToEnc, casters::CastTypePure},
        ConstEnc, MirBuiltinEnc,
    },
};

use crate::encoders::{
    lifted::{
        cast::CastArgs, func_app_ty_params::LiftedFuncAppTyParamsEnc,
        func_def_ty_params::LiftedTyParamsEnc, generic::LiftedGeneric,
        rust_ty_cast::RustTyCastersEnc,
    },
    mir_base::MirBaseEnc,
    mir_pure::PureKind,
    rust_ty_snapshots::RustTySnapshotsEnc,
    sym::{backwards::mk_backwards_method, expr::SymExprEncoder},
    sym_pure::{
        PrustiPathConditions, PrustiSemantics, PrustiSubsts, PrustiSymValSynthetic,
        PrustiSymValSyntheticData, PrustiSymValue, SymPureEncResult,
    },
    sym_spec::SymSpecEnc,
    FunctionCallTaskDescription, MirBuiltinEncTask, PureFunctionEnc, SpecEnc, SpecEncTask,
    SymFunctionEnc, SymPureEnc, SymPureEncTask,
};

use super::SymImpureEnc;
pub struct ForwardBackwardsShared<'vir> {
    ty_arg_decls: &'vir [LiftedGeneric<'vir>],
    pub symvar_locals: Vec<vir::Local<'vir>>,
    pub result_local: vir::Local<'vir>,
    pub type_assertion_stmts: Vec<vir::Stmt<'vir>>,
    pub decl_stmts: Vec<vir::Stmt<'vir>>,
    pub arg_count: usize,
}

impl<'vir> ForwardBackwardsShared<'vir> {
    pub fn arg_locals(&self) -> &[vir::Local<'vir>] {
        &self.symvar_locals[..self.arg_count]
    }

    pub fn new<'sym, 'tcx, 'deps>(
        symex_result: &SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
        substs: ty::GenericArgsRef<'tcx>,
        body: &mir::Body<'tcx>,
        deps: &'deps mut TaskEncoderDependencies<'vir, SymImpureEnc>,
    ) -> ForwardBackwardsShared<'vir>
    where
        'vir: 'tcx,
        'tcx: 'vir,
    {
        vir::with_vcx(|vcx| {
            let symvar_locals = symex_result
                .symvars
                .iter()
                .enumerate()
                .map(|(idx, ty)| {
                    vcx.mk_local(
                        vir_format!(vcx, "s{}", idx),
                        deps.require_ref::<RustTySnapshotsEnc>(*ty)
                            .unwrap()
                            .generic_snapshot
                            .snapshot,
                    )
                })
                .collect::<Vec<_>>();
            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut type_assertion_stmts = vec![];
            for (local, symvar) in symvar_locals.iter().zip(symex_result.symvars.iter()) {
                if let Some(expr) =
                    mk_type_assertion(vcx, deps, vcx.mk_local_ex(local.name, local.ty), *symvar)
                {
                    type_assertion_stmts.push(vcx.mk_inhale_stmt(expr));
                }
            }
            let result_local = vcx.mk_local(
                "res",
                deps.require_ref::<RustTySnapshotsEnc>(body.local_decls.iter().next().unwrap().ty)
                    .unwrap()
                    .generic_snapshot
                    .snapshot,
            );
            let mut decl_stmts = vec![];
            for arg in ty_arg_decls {
                decl_stmts.push(vcx.mk_local_decl_stmt(arg.decl(), None));
            }

            decl_stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            for local in symvar_locals.iter() {
                decl_stmts
                    .push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
            }
            Self {
                arg_count: body.arg_count,
                ty_arg_decls,
                symvar_locals,
                type_assertion_stmts,
                decl_stmts,
                result_local,
            }
        })
    }
}
