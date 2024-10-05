use pcs::{combined_pcs::BodyWithBorrowckFacts, utils::Place};
use prusti_interface::environment::{mir_storage, Procedure};
use prusti_rustc_interface::{
    ast,
    ast::Local,
    hir::{self, Mutability},
    index::IndexVec,
    middle::{
        mir::{self, PlaceElem, VarDebugInfo},
        thir::{self, Thir},
        ty::{self, GenericArgsRef, TyCtxt, TyKind},
    },
    span::{def_id::DefId, symbol::Ident, Span, Symbol},
    target::abi::{FieldIdx, FIRST_VARIANT},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    marker::PhantomData,
};
use symbolic_execution::{
    context::SymExContext,
    encoder::Encoder,
    heap::{HeapData, SymbolicHeap},
    path::Path,
    path_conditions::PathConditions,
    results::{ResultAssertion, ResultAssertions, ResultPath},
    semantics::VerifierSemantics,
    terminator::{FunctionCallEffects, FunctionCallResult},
    transform::{BaseSymValueTransformer, SymValueTransformer},
    value::{
        AggregateKind, CanSubst, Substs, SymValue, SymValueData, SymValueKind, SymVar,
        SyntheticSymValue, Ty,
    },
    visualization::{OutputMode, VisFormat},
    Assertion, SymExParams, SymbolicExecution,
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
// TODO: replace uses of `CapabilityEnc` with `SnapshotEnc`
use crate::{
    debug::fn_debug_name,
    encoders::{
        sym_pure::{PrustiSymValSyntheticData, PrustiSymValue},
        CapabilityEnc, ConstEnc, MirBuiltinEnc, SnapshotEnc, ViperTupleEnc,
    },
};

pub fn find_node_by_span<'thir, 'tcx>(
    _tcx: TyCtxt<'tcx>,
    body: &'thir Thir<'tcx>,
    target_span: Span,
) -> Option<&'thir thir::Expr<'tcx>> {
    body.exprs.iter().find(|expr| expr.span == target_span)
}

pub fn thir_node_to_sym_expr<'sym, 'tcx>(
    arena: &'sym SymExContext<'tcx>,
    mir_body: &mir::Body<'tcx>,
    thir: &Thir<'tcx>,
    input_idents: &HashMap<Symbol, (usize, ty::Ty<'tcx>)>,
    node: &thir::Expr<'tcx>,
) -> PrustiSymValue<'sym, 'tcx, SymVar> {
    match &node.kind {
        thir::ExprKind::Deref { arg } => arena.mk_projection(
            mir::ProjectionElem::Deref,
            thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*arg]),
        ),
        thir::ExprKind::UpvarRef { var_hir_id, .. } => {
            let hir_node = arena.tcx.hir_node(var_hir_id.0);
            let ident = match hir_node {
                hir::Node::Pat(pat) => match pat.kind {
                    hir::PatKind::Path(hir::QPath::Resolved(_, path)) => {
                        assert!(path.segments.len() == 1);
                        path.segments[0].ident.name
                    }
                    hir::PatKind::Binding(_, _, ident, _) => ident.name,
                    _ => todo!("{:?}", pat.kind),
                },
                _ => todo!("{:?}", hir_node),
            };
            let (index, _ty) = input_idents.get(&ident).unwrap();
            arena.mk_var(SymVar::nth_input(*index), node.ty)
        }
        thir::ExprKind::VarRef { id } => {
            let hir_node = arena.tcx.hir_node(id.0);
            let ident = match hir_node {
                hir::Node::Pat(pat) => match pat.kind {
                    hir::PatKind::Path(hir::QPath::Resolved(_, path)) => {
                        assert!(path.segments.len() == 1);
                        path.segments[0].ident.name
                    }
                    hir::PatKind::Binding(_, _, ident, _) => ident.name,
                    _ => todo!("{:?}", pat.kind),
                },
                _ => todo!("{:?}", hir_node),
            };
            let (index, ty) = input_idents.get(&ident).unwrap();
            arena.mk_var(SymVar::nth_input(*index), *ty)
        }
        thir::ExprKind::Field {
            lhs,
            variant_index,
            name,
        } => {
            let base =
                thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*lhs]);
            match base.ty(arena.tcx).rust_ty().kind() {
                rustc_type_ir::TyKind::Adt(def, substs) => {
                    let variant = def.variant(*variant_index);
                    let field = &variant.fields[*name];
                    arena.mk_projection(
                        mir::ProjectionElem::Field(*name, field.ty(arena.tcx, substs)),
                        base,
                    )
                }
                rustc_type_ir::TyKind::Tuple(tys) => arena.mk_projection(
                    mir::ProjectionElem::Field(*name, tys[name.as_usize()]),
                    base,
                ),
                _ => todo!(),
            }
        }
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let lhs = thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*lhs]);
            let rhs = thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*rhs]);
            let op = *op;
            arena.mk_bin_op(node.ty, op, lhs, rhs)
        }
        thir::ExprKind::Call {
            args,
            fn_span,
            ..
        } => {
            let sym_args = args
                .iter()
                .map(|arg| {
                    thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*arg])
                })
                .collect::<Vec<_>>();
            /*
             * We may have monomorphized/substitued the mir, so we get the substs from mir rather than thir
             */
            let (def_id, substs) = mir_body
                .basic_blocks
                .iter()
                .find_map(|bb| match &bb.terminator().kind {
                    mir::TerminatorKind::Call {
                        func,
                        args: _,
                        destination: _,
                        target: _,
                        unwind: _,
                        call_source: _,
                        fn_span: mir_fn_span,
                    } => {
                        if fn_span == mir_fn_span {
                            match func.ty(mir_body, arena.tcx).kind() {
                                ty::TyKind::FnDef(def_id, substs) => Some((*def_id, substs)),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                })
                .unwrap();
            arena.mk_synthetic(arena.alloc(PrustiSymValSyntheticData::PureFnCall(
                def_id,
                substs,
                arena.alloc_slice(&sym_args),
            )))
        }
        thir::ExprKind::Scope { value, .. } => {
            thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*value])
        }
        thir::ExprKind::Borrow { borrow_kind, arg } => {
            let arg = thir_node_to_sym_expr(arena, mir_body, thir, input_idents, &thir.exprs[*arg]);
            arena.mk_ref(arg, borrow_kind.mutability())
        }
        other => {
            panic!("Unsupported expression kind: {:?}", other);
        }
    }
}
