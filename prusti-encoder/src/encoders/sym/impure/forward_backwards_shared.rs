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
    pub symvars: BTreeMap<SymVar, (ty::Ty<'tcx>, vir::Local<'vir>)>,
    pub ty_args: &'vir [LiftedGeneric<'vir>],
    pub result_local: vir::Local<'vir>,
    pub type_assertion_stmts: Vec<vir::Stmt<'vir>>,
    pub decl_stmts: Vec<vir::Stmt<'vir>>,
    pub arg_count: usize,
    /// The result type of the *forwards* function
    pub result_ty: ty::Ty<'tcx>,
}

impl<'vir, 'tcx> ForwardBackwardsShared<'vir, 'tcx> {
    pub fn symvar_ty(&self, symvar: SymVar) -> ty::Ty<'tcx> {
        self.symvars.get(&symvar).unwrap().0
    }

    pub fn nth_input_ty(&self, i: usize) -> ty::Ty<'tcx> {
        self.symvars.get(&SymVar::nth_input(i)).unwrap().0
    }

    pub fn symvar_locals(&self) -> Vec<vir::Local<'vir>> {
        self.symvars.values().map(|(_, l)| *l).collect()
    }

    pub fn arg_locals(&self) -> Vec<vir::Local<'vir>> {
        (0..self.arg_count)
            .map(|i| self.symvars.get(&SymVar::nth_input(i)).unwrap().1)
            .collect::<Vec<_>>()
    }

    pub fn ty_and_arg_decls(&self) -> Vec<vir::LocalDecl<'vir>> {
        vir::with_vcx(|vcx| {
            self.ty_args
                .iter()
                .map(|l| l.decl())
                .chain(
                    self.arg_locals()
                        .iter()
                        .map(|l| vcx.mk_local_decl(l.name, l.ty)),
                )
                .collect()
        })
    }

    pub fn new<'sym, 'deps>(
        symex_result: &SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
        substs: ty::GenericArgsRef<'tcx>,
        body: &mir::Body<'tcx>,
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
                    (
                        SymVar::Input(local),
                        (
                            ty,
                            vcx.mk_local(
                                vir_format!(vcx, "i{}", local.as_usize()),
                                deps.require_ref::<RustTySnapshotsEnc>(ty)
                                    .unwrap()
                                    .generic_snapshot
                                    .snapshot,
                            ),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let fresh_symvars = symex_result
                .fresh_symvars
                .iter()
                .enumerate()
                .map(|(idx, ty)| {
                    (
                        SymVar::Fresh(idx),
                        (
                            *ty,
                            vcx.mk_local(
                                vir_format!(vcx, "f{}", idx),
                                deps.require_ref::<RustTySnapshotsEnc>(*ty)
                                    .unwrap()
                                    .generic_snapshot
                                    .snapshot,
                            ),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let ty_args = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut type_assertion_stmts = vec![];
            let result_local = vcx.mk_local(
                "res",
                deps.require_ref::<RustTySnapshotsEnc>(body.local_decls.iter().next().unwrap().ty)
                    .unwrap()
                    .generic_snapshot
                    .snapshot,
            );
            let mut decl_stmts = vec![];
            for arg in ty_args {
                decl_stmts.push(vcx.mk_local_decl_stmt(arg.decl(), None));
            }

            decl_stmts.push(
                vcx.mk_local_decl_stmt(vcx.mk_local_decl(result_local.name, result_local.ty), None),
            );

            let symvars = input_symvars
                .into_iter()
                .chain(fresh_symvars.into_iter())
                .collect::<BTreeMap<_, _>>();

            for (_, (ty, local)) in symvars.iter() {
                decl_stmts
                    .push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(local.name, local.ty), None));
                if let Some(expr) =
                    mk_type_assertion(vcx, deps, vcx.mk_local_ex(local.name, local.ty), *ty)
                {
                    type_assertion_stmts.push(vcx.mk_inhale_stmt(expr));
                }
            }
            Self {
                arg_count: body.arg_count,
                ty_args,
                type_assertion_stmts,
                decl_stmts,
                result_local,
                result_ty: body.local_decls.iter().next().unwrap().ty,
                symvars,
            }
        })
    }
}
