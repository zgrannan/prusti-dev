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
        mir::{self, interpret::Scalar, Local, LocalDecl, ProjectionElem},
        ty::{self, GenericArgs},
    },
    span::def_id::{DefId, LocalDefId},
};
use rustc_type_ir::InferTy::FreshFloatTy;
use std::hash::{Hash, Hasher};
use symbolic_execution::{
    context::SymExContext,
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    results::{ResultPath, SymbolicExecutionResult},
    value::{Substs, SymValueData, SymValueKind, SymVar},
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
        sym_spec::SymSpec,
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
pub struct ForwardBackwardsShared<'vir, 'tcx> {
    pub symvar_locals: BTreeMap<SymVar, vir::Local<'vir>>,
    pub symvar_tys: BTreeMap<SymVar, ty::Ty<'tcx>>,
    pub ty_args: &'vir [LiftedGeneric<'vir>],
    pub result_local: vir::Local<'vir>,
    /// Type assertions statements for inputs, followed by user-defined preconditions
    pub precondition_exprs: &'vir [vir::Expr<'vir>],
    /// Type assertions statements for fresh symvars (inputs type assertions are in `precondition_exprs`)
    pub body_type_assertion_stmts: Vec<vir::Stmt<'vir>>,
    pub decl_stmts: Vec<vir::Stmt<'vir>>,
    pub arg_count: usize,
    /// The result type of the *forwards* function
    pub result_ty: ty::Ty<'tcx>,
}

impl<'vir, 'tcx> ForwardBackwardsShared<'vir, 'tcx> {
    pub fn precondition_stmts(&self) -> Vec<vir::Stmt<'vir>> {
        vir::with_vcx(|vcx| {
            self.precondition_exprs
                .iter()
                .map(|expr| vcx.mk_inhale_stmt(*expr))
                .collect()
        })
    }

    pub fn symvar_ty(&self, symvar: SymVar) -> ty::Ty<'tcx> {
        self.symvar_tys[&symvar]
    }

    pub fn nth_input_ty(&self, i: usize) -> ty::Ty<'tcx> {
        self.symvar_tys[&SymVar::nth_input(i)]
    }

    pub fn nth_input_local(&self, i: usize) -> vir::Local<'vir> {
        self.symvar_locals[&SymVar::nth_input(i)]
    }

    pub fn nth_input_expr(&self, i: usize) -> vir::Expr<'vir> {
        let local = self.symvar_locals[&SymVar::nth_input(i)];
        vir::with_vcx(|vcx| vcx.mk_local_ex_local(local))
    }

    pub fn symvar_locals(&self) -> Vec<vir::Local<'vir>> {
        self.symvar_locals.values().cloned().collect()
    }

    pub fn symvar_vir_ty(&self, symvar: SymVar) -> vir::Type<'vir> {
        self.symvar_locals[&symvar].ty
    }

    pub fn arg_locals(&self) -> Vec<vir::Local<'vir>> {
        (0..self.arg_count)
            .map(|i| self.symvar_locals[&SymVar::nth_input(i)])
            .collect::<Vec<_>>()
    }

    pub fn new<'sym, 'deps>(
        symex_result: &SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
        substs: ty::GenericArgsRef<'tcx>,
        symvar_locals: BTreeMap<SymVar, vir::Local<'vir>>,
        spec_precondition_exprs: Vec<vir::Expr<'vir>>,
        body: &mir::Body<'tcx>,
        result_local: vir::Local<'vir>,
        ty_args: &'vir [LiftedGeneric<'vir>],
        deps: &'deps mut TaskEncoderDependencies<'vir, SymImpureEnc>,
    ) -> ForwardBackwardsShared<'vir, 'tcx>
    where
        'vir: 'tcx,
        'tcx: 'vir,
    {
        vir::with_vcx(|vcx| {
            let input_symvars = body
                .args_iter()
                .map(|local| {
                    let ty = body.local_decls[local].ty;
                    (SymVar::Input(local), ty)
                })
                .collect::<BTreeMap<_, _>>();
            let fresh_symvars = symex_result
                .fresh_symvars
                .iter()
                .enumerate()
                .map(|(idx, ty)| (SymVar::Fresh(idx), *ty))
                .collect::<BTreeMap<_, _>>();

            let input_ty_assertions = mk_ty_assertions(deps, &input_symvars, &symvar_locals);
            let fresh_ty_assertions = mk_ty_assertions(deps, &fresh_symvars, &symvar_locals);

            let body_type_assertion_stmts = fresh_ty_assertions
                .into_iter()
                .map(|expr| vcx.mk_inhale_stmt(expr))
                .collect::<Vec<_>>();

            let mut decl_stmts = ty_args
                .into_iter()
                .map(|arg| vcx.mk_local_decl_stmt(arg.decl(), None))
                .collect::<Vec<_>>();

            decl_stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            decl_stmts.extend(
                symvar_locals
                    .iter()
                    .map(|(_, local)| {
                        vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None)
                    })
                    .collect::<Vec<_>>(),
            );

            let symvar_tys: BTreeMap<SymVar, ty::Ty<'tcx>> = input_symvars
                .into_iter()
                .chain(fresh_symvars.into_iter())
                .collect::<BTreeMap<_, _>>();

            Self {
                arg_count: body.arg_count,
                ty_args,
                body_type_assertion_stmts,
                decl_stmts,
                result_local,
                result_ty: body.local_decls.iter().next().unwrap().ty,
                symvar_locals,
                symvar_tys,
                precondition_exprs: vcx.alloc_slice(
                    &input_ty_assertions
                        .into_iter()
                        .chain(spec_precondition_exprs)
                        .collect::<Vec<_>>(),
                ),
            }
        })
    }
}

fn mk_ty_assertions<'tcx: 'vir, 'vir: 'tcx, 'deps>(
    deps: &'deps mut TaskEncoderDependencies<'vir, SymImpureEnc>,
    symvar_tys: &BTreeMap<SymVar, ty::Ty<'tcx>>,
    symvar_locals: &BTreeMap<SymVar, vir::Local<'vir>>,
) -> Vec<vir::Expr<'vir>> {
    vir::with_vcx(|vcx| {
        symvar_tys
            .iter()
            .flat_map(|(var, ty)| {
                let local = symvar_locals[var];
                mk_type_assertion(vcx, deps, vcx.mk_local_ex(local.name, local.ty), *ty)
            })
            .collect::<Vec<_>>()
    })
}
