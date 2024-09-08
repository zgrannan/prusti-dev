use pcs::{combined_pcs::BodyWithBorrowckFacts, utils::Place};
use prusti_interface::environment::Procedure;
use prusti_rustc_interface::{
    ast,
    ast::Local,
    hir::{self, intravisit, Mutability},
    index::IndexVec,
    middle::{
        mir::{self, PlaceElem, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt, TyKind},
    },
    span::{def_id::DefId, symbol::Ident, Span},
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
    path::{InputPlace, OldMap, OldMapEncoder, Path, StructureTerm},
    path_conditions::PathConditions,
    results::ResultPath,
    semantics::VerifierSemantics,
    terminator::{FunctionCallEffects, FunctionCallResult},
    transform::{BaseSymValueTransformer, SymValueTransformer},
    value::{
        AggregateKind, CanSubst, Substs, SymValue, SymValueData, SymValueKind, SymVar,
        SyntheticSymValue, Ty,
    },
    visualization::{OutputMode, VisFormat},
    SymExParams, SymbolicExecution,
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
// TODO: replace uses of `CapabilityEnc` with `SnapshotEnc`
use crate::{
    debug::fn_debug_name,
    encoders::{CapabilityEnc, ConstEnc, MirBuiltinEnc, SnapshotEnc, ViperTupleEnc},
};

use super::{mir_base::MirBaseEnc, mir_pure::PureKind, spec::with_def_spec};

pub struct SymPureEnc;

#[derive(Clone, Debug)]
pub enum SymPureEncError {
    UnsupportedStatement,
    UnsupportedTerminator,
}

// TODO: does this need to be `&'vir [..]`?
type ExprInput<'vir> = (DefId, &'vir [vir::Expr<'vir>]);
type ExprRet<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone, Debug)]
pub struct SymPureEncOutput<'sym, 'tcx> {
    pub expr: PrustiSymValue<'sym, 'tcx>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymPureEncTask<'tcx> {
    pub kind: PureKind,
    pub parent_def_id: DefId,             // ID of the function
    pub param_env: ty::ParamEnv<'tcx>,    // param environment at the usage site
    pub substs: ty::GenericArgsRef<'tcx>, // type substitutions at the usage site
    pub caller_def_id: Option<DefId>,     // Caller/Use DefID
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymPureEncResult<'sym, 'tcx> {
    pub paths: Vec<(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)>,
    pub debug_id: Option<String>,
}

impl<'sym, 'tcx> VisFormat for SymPureEncResult<'sym, 'tcx> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        self.paths
            .iter()
            .map(|(path_conditions, value)| {
                format!(
                    "{} ==> {}",
                    path_conditions.to_vis_string(tcx, debug_info, mode),
                    value.to_vis_string(tcx, debug_info, mode)
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl<'sym, 'tcx> SymPureEncResult<'sym, 'tcx> {
    pub fn from_sym_value(value: PrustiSymValue<'sym, 'tcx>) -> Self {
        Self {
            paths: vec![(PathConditions::new(), value)].into_iter().collect(),
            debug_id: None,
        }
    }

    pub fn into_iter(
        self,
    ) -> impl Iterator<Item = (PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.paths.into_iter()
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = &(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        self.paths.iter()
    }

    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
    ) -> Self {
        let paths = self
            .paths
            .into_iter()
            .map(|(path_conditions, value)| {
                (
                    path_conditions.apply_transformer(arena, transformer),
                    value.apply_transformer(arena, transformer),
                )
            })
            .collect();
        Self {
            paths,
            debug_id: self.debug_id,
        }
    }

    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs PrustiSubsts<'sym, 'tcx>,
    ) -> Self {
        let paths = self
            .paths
            .into_iter()
            .map(|(path_conditions, value)| {
                (
                    path_conditions.subst(arena, substs),
                    value.subst(arena, substs),
                )
            })
            .collect();
        Self {
            paths,
            debug_id: self.debug_id,
        }
    }
}

pub struct PrustiSemantics<'sym, 'tcx>(pub PhantomData<&'sym &'tcx ()>);

pub type PrustiSymValSynthetic<'sym, 'tcx, V = SymVar> =
    &'sym PrustiSymValSyntheticData<'sym, 'tcx, V>;

#[derive(Eq, Debug, PartialEq, Clone)]
pub enum PrustiSymValSyntheticData<'sym, 'tcx, V = SymVar> {
    And(PrustiSymValue<'sym, 'tcx, V>, PrustiSymValue<'sym, 'tcx, V>),
    If(
        PrustiSymValue<'sym, 'tcx, V>,
        PrustiSymValue<'sym, 'tcx, V>,
        PrustiSymValue<'sym, 'tcx, V>,
    ),
    PureFnCall(
        DefId,
        GenericArgsRef<'tcx>,
        &'sym [PrustiSymValue<'sym, 'tcx, V>],
    ),
    Result(ty::Ty<'tcx>),
    VirLocal(&'sym str, ty::Ty<'tcx>),
    Old(PrustiSymValue<'sym, 'tcx, V>),
}

impl<'sym, 'tcx> VisFormat for &'sym PrustiSymValSyntheticData<'sym, 'tcx> {
    fn to_vis_string(
        &self,
        tcx: Option<ty::TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match self {
            PrustiSymValSyntheticData::And(l, r) => format!(
                "({} && {})",
                l.to_vis_string(tcx, debug_info, mode),
                r.to_vis_string(tcx, debug_info, mode)
            ),
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => format!(
                "({} ? {} : {})",
                cond.to_vis_string(tcx, debug_info, mode),
                then_expr.to_vis_string(tcx, debug_info, mode),
                else_expr.to_vis_string(tcx, debug_info, mode)
            ),
            PrustiSymValSyntheticData::PureFnCall(def_id, _substs, args) => vir::with_vcx(|vcx| {
                let fn_name = vcx.tcx().item_name(*def_id);
                let args_str = args
                    .iter()
                    .map(|arg| arg.to_vis_string(tcx, debug_info, mode))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", fn_name, args_str)
            }),
            PrustiSymValSyntheticData::Result(_ty) => "result".to_string(),
            PrustiSymValSyntheticData::VirLocal(name, _) => name.to_string(),
            PrustiSymValSyntheticData::Old(value) => {
                format!("old({})", value.to_vis_string(tcx, debug_info, mode))
            }
        }
    }
}

impl<'sym, 'tcx> std::fmt::Display for PrustiSymValSyntheticData<'sym, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            PrustiSymValSyntheticData::And(_, _) => todo!(),
            PrustiSymValSyntheticData::If(_, _, _) => todo!(),
            PrustiSymValSyntheticData::PureFnCall(def_id, _, args) => {
                let fn_name = format!("{:?}", def_id);
                let args_str = args
                    .iter()
                    .map(|arg| format!("{}", arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}({})", fn_name, args_str)
            }
            PrustiSymValSyntheticData::Result(_) => todo!(),
            PrustiSymValSyntheticData::VirLocal(_, _) => todo!(),
            PrustiSymValSyntheticData::Old(..) => todo!(),
        }
    }
}
impl<'sym, 'tcx> CanSubst<'sym, 'tcx> for PrustiSymValSynthetic<'sym, 'tcx> {
    fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        _tcx: ty::TyCtxt<'tcx>,
        substs: &Substs<'sym, 'tcx, Self>,
    ) -> Self {
        match self {
            PrustiSymValSyntheticData::And(l, r) => arena.alloc(PrustiSymValSyntheticData::And(
                l.subst(arena, substs),
                r.subst(arena, substs),
            )),
            PrustiSymValSyntheticData::PureFnCall(def_id, ty_substs, args) => {
                arena.alloc(PrustiSymValSyntheticData::PureFnCall(
                    *def_id,
                    ty_substs,
                    arena.alloc_slice(
                        &(args
                            .iter()
                            .map(|arg| arg.subst(arena, substs))
                            .collect::<Vec<_>>()),
                    ),
                ))
            }
            PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => {
                arena.alloc(PrustiSymValSyntheticData::If(
                    cond.subst(arena, substs),
                    then_expr.subst(arena, substs),
                    else_expr.subst(arena, substs),
                ))
            }
            PrustiSymValSyntheticData::Result(_) => todo!(),
            PrustiSymValSyntheticData::VirLocal(_, _) => todo!(),
            PrustiSymValSyntheticData::Old(..) => self,
        }
    }
}

impl<'sym, 'tcx, V> SyntheticSymValue<'sym, 'tcx> for PrustiSymValSynthetic<'sym, 'tcx, V> {
    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match &self {
            PrustiSymValSyntheticData::And(_, _) => Ty::new(tcx.types.bool, None),
            PrustiSymValSyntheticData::If(_, t, _) => t.ty(tcx),
            PrustiSymValSyntheticData::PureFnCall(def_id, substs, _) => Ty::new(
                tcx.fn_sig(def_id)
                    .instantiate(tcx, substs)
                    .output()
                    .skip_binder(),
                None,
            ),
            PrustiSymValSyntheticData::Result(ty) => Ty::new(*ty, None),
            PrustiSymValSyntheticData::VirLocal(_, ty) => Ty::new(*ty, None),
            PrustiSymValSyntheticData::Old(val) => val.ty(tcx),
        }
    }

    fn optimize(self, _arena: &'sym SymExContext<'tcx>, _tcx: ty::TyCtxt<'tcx>) -> Self {
        // TODO
        self
        // match &self {
        //     PrustiSymValSyntheticData::And(lhs, rhs) => arena.alloc(
        //         PrustiSymValSyntheticData::And(lhs.optimize(arena, tcx), rhs.optimize(arena, tcx)),
        //     ),
        //     PrustiSymValSyntheticData::If(cond, then_expr, else_expr) => {
        //         arena.alloc(PrustiSymValSyntheticData::If(
        //             cond.optimize(arena, tcx),
        //             then_expr.optimize(arena, tcx),
        //             else_expr.optimize(arena, tcx),
        //         ))
        //     }
        //     PrustiSymValSyntheticData::PureFnCall(def_id, ty_substs, args) => {
        //         arena.alloc(PrustiSymValSyntheticData::PureFnCall(
        //             *def_id,
        //             ty_substs,
        //             arena.alloc_slice(
        //                 &(args
        //                     .iter()
        //                     .map(|arg| arg.optimize(arena, tcx))
        //                     .collect::<Vec<_>>()),
        //             ),
        //         ))
        //     }
        //     PrustiSymValSyntheticData::Result(_) => self,
        //     PrustiSymValSyntheticData::VirLocal(_, _) => self,
        //     PrustiSymValSyntheticData::Old(_) => self,
        // }
    }
}

pub type PrustiPathConditions<'sym, 'tcx> =
    PathConditions<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;
pub type PrustiSymValue<'sym, 'tcx, V = SymVar> =
    SymValue<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx, V>, V>;
pub type PrustiSubsts<'sym, 'tcx> = Substs<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>;

struct SpanFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    target_span: Span,
    found_expr: Option<&'tcx hir::Expr<'tcx>>, // Store the found expression
}

impl<'tcx> intravisit::Visitor<'tcx> for SpanFinder<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        // Compare the span of this expression with the target span
        if expr.span == self.target_span {
            self.found_expr = Some(expr);
        }
        // Continue traversing the expression tree
        intravisit::walk_expr(self, expr);
    }
}

fn find_node_by_span<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'tcx hir::Body<'tcx>,
    target_span: Span,
) -> Option<&'tcx hir::Expr<'tcx>> {
    // Create the SpanFinder visitor
    let mut visitor = SpanFinder {
        tcx,
        target_span,
        found_expr: None,
    };

    // Start walking the body of the function (HIR tree)
    intravisit::walk_body(&mut visitor, body);

    // Return the found node, if any
    visitor.found_expr
}

fn hir_node_to_sym_expr<'sym, 'tcx>(
    arena: &'sym SymExContext<'tcx>,
    input_idents: &HashMap<Ident, (usize, ty::Ty<'tcx>)>,
    node: hir::Expr<'tcx>,
) -> PrustiSymValue<'sym, 'tcx, SymVar> {
    match node.kind {
        hir::ExprKind::Unary(hir::UnOp::Deref, expr) => arena.mk_projection(
            mir::ProjectionElem::Deref,
            hir_node_to_sym_expr(arena, input_idents, *expr),
        ),
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => {
            assert!(path.segments.len() == 1);
            let segment = path.segments[0];
            let (index, ty) = input_idents.get(&segment.ident).unwrap();
            arena.mk_var(SymVar::nth_input(*index), *ty)
        }
        hir::ExprKind::Field(expr, field) => {
            let base = hir_node_to_sym_expr(arena, input_idents, *expr);
            match base.ty(arena.tcx).rust_ty().kind() {
                rustc_type_ir::TyKind::Adt(def, substs) => {
                    let variant = def.variant(FIRST_VARIANT);
                    let field_index = variant
                        .fields
                        .iter()
                        .position(|variant_field| variant_field.name == field.name)
                        .unwrap();
                    let field_index = FieldIdx::from_usize(field_index);
                    let field = &variant.fields[field_index];
                    arena.mk_projection(
                        mir::ProjectionElem::Field(field_index, field.ty(arena.tcx, substs)),
                        base,
                    )
                }
                rustc_type_ir::TyKind::Tuple(tys) => {
                    let field_idx = field.name.as_str().parse::<usize>().unwrap();
                    arena.mk_projection(
                        mir::ProjectionElem::Field(FieldIdx::from_usize(field_idx), tys[field_idx]),
                        base,
                    )
                }
                _ => todo!(),
            }
        }
        hir::ExprKind::Binary(op, e1, e2) => {
            let e1 = hir_node_to_sym_expr(arena, input_idents, *e1);
            let e2 = hir_node_to_sym_expr(arena, input_idents, *e2);
            let op = match op.node {
                hir::BinOpKind::Add => mir::BinOp::Add,
                _ => todo!(),
            };
            arena.mk_bin_op(e1.ty(arena.tcx).rust_ty(), op, e1, e2)
        }
        hir::ExprKind::Call(func, args) => {
            let args = args
                .iter()
                .map(|arg| hir_node_to_sym_expr(arena, input_idents, *arg))
                .collect::<Vec<_>>();
            let def_id = match func.kind {
                hir::ExprKind::Path(hir::QPath::Resolved(ty, path)) => match path.res {
                    hir::def::Res::Def(_, def_id) => def_id,
                    hir::def::Res::PrimTy(_) => todo!(),
                    hir::def::Res::SelfTyParam { trait_ } => todo!(),
                    hir::def::Res::SelfTyAlias {
                        alias_to,
                        forbid_generic,
                        is_trait_impl,
                    } => todo!(),
                    hir::def::Res::SelfCtor(_) => todo!(),
                    hir::def::Res::Local(_) => todo!(),
                    hir::def::Res::ToolMod => todo!(),
                    hir::def::Res::NonMacroAttr(_) => todo!(),
                    hir::def::Res::Err => todo!(),
                },
                _ => todo!(),
            };
            arena.mk_synthetic(arena.alloc(PrustiSymValSyntheticData::PureFnCall(
                def_id,
                ty::GenericArgs::identity_for_item(arena.tcx, def_id),
                arena.alloc_slice(&args),
            )))
        }
        other => {
            panic!("Unsupported expression kind: {:?}", other);
        }
    }
}

impl<'sym, 'tcx> VerifierSemantics<'sym, 'tcx> for PrustiSemantics<'sym, 'tcx> {
    type SymValSynthetic = PrustiSymValSynthetic<'sym, 'tcx, SymVar>;
    type OldMapSymValSynthetic = PrustiSymValSynthetic<'sym, 'tcx, InputPlace<'tcx>>;
    fn encode_fn_call<'mir>(
        span: Span,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        old_map: &mut OldMap<'sym, 'tcx, Self::OldMapSymValSynthetic>,
        args: &Vec<&mir::Operand<'tcx>>,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic, Self::OldMapSymValSynthetic>>
    {
        vir::with_vcx(|vcx| {
            let fn_name = vcx.tcx().def_path_str(def_id);
            let mut heap = SymbolicHeap::new(heap, vcx.tcx(), sym_ex.body, sym_ex.arena);
            if fn_name == "prusti_contracts::old" {
                eprintln!("def_id: {:?}", def_id);
                let (_, _, body_id) = vcx
                    .tcx()
                    .hir_node_by_def_id(sym_ex.def_id)
                    .expect_item()
                    .expect_fn();
                let thir_body = vcx.tcx().thir_body(sym_ex.def_id);
                panic!("thir_body: {:?}", thir_body.unwrap().0.borrow());
                let body = vcx.tcx().hir().body(body_id);
                let input_idents = body
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        (
                            p.pat.simple_ident().unwrap(),
                            (i, sym_ex.body.local_decls[mir::Local::from_usize(i + 1)].ty),
                        )
                    })
                    .collect::<HashMap<_, _>>();
                let node = find_node_by_span(vcx.tcx(), &body, span).unwrap();
                let arg = match node.kind {
                    hir::ExprKind::Call(_, args) => args[0],
                    _ => {
                        unreachable!()
                    }
                };
                let value =
                    sym_ex
                        .arena
                        .mk_synthetic(sym_ex.arena.alloc(PrustiSymValSyntheticData::Old(
                            hir_node_to_sym_expr(sym_ex.arena, &input_idents, arg),
                        )));
                return Some(FunctionCallEffects {
                    result: FunctionCallResult::Value {
                        value,
                        old_map_value: None,
                        postcondition: None,
                    },
                    precondition_assertion: None,
                    snapshot: None,
                });
            }
            let encoded_args: Vec<PrustiSymValue<'sym, 'tcx, SymVar>> = args
                .iter()
                .map(|arg| sym_ex.encode_operand(&mut heap, arg))
                .collect();
            let old_map_encoded_args: Vec<PrustiSymValue<'sym, 'tcx, InputPlace<'tcx>>> = args
                .iter()
                .map(|arg| {
                    let encoder = sym_ex.old_map_encoder();
                    encoder.encode_operand(old_map, arg)
                })
                .collect();
            let old_map_encoded_args: &'sym [PrustiSymValue<'sym, 'tcx, InputPlace<'tcx>>] =
                sym_ex.arena.alloc_slice(&old_map_encoded_args);
            let args = sym_ex.arena.alloc_slice(&encoded_args);
            match fn_name.as_str() {
                "prusti_contracts::before_expiry" => {
                    return Some(FunctionCallEffects {
                        precondition_assertion: None,
                        result: FunctionCallResult::Value {
                            value: args[0],
                            old_map_value: None,
                            postcondition: None,
                        },
                        snapshot: None,
                    });
                }
                "std::boxed::Box::<T>::new" => {
                    assert_eq!(args.len(), 1);
                    let output_ty = vcx
                        .tcx()
                        .fn_sig(def_id)
                        .instantiate(vcx.tcx(), substs)
                        .output()
                        .skip_binder();
                    let substs = if let ty::TyKind::Adt(_, substs) = output_ty.kind() {
                        substs
                    } else {
                        unreachable!()
                    };
                    return Some(FunctionCallEffects {
                        precondition_assertion: None,
                        result: FunctionCallResult::Value {
                            old_map_value: None,
                            value: sym_ex.arena.mk_aggregate(
                                AggregateKind::Rust(
                                    mir::AggregateKind::Adt(
                                        vcx.tcx().lang_items().owned_box().unwrap(),
                                        FIRST_VARIANT,
                                        substs,
                                        None,
                                        None,
                                    ),
                                    output_ty,
                                ),
                                args,
                            ),
                            postcondition: None,
                        },
                        snapshot: None,
                    });
                }
                _ => {}
            }

            let is_pure = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                proc_spec.kind.is_pure().unwrap_or_default()
            })
            .unwrap_or(
                fn_name == "std::cmp::PartialEq::eq" || fn_name == "std::cmp::PartialEq::ne",
            );
            if is_pure {
                let old_map_value: SymValue<
                    'sym,
                    'tcx,
                    PrustiSymValSynthetic<'sym, 'tcx, InputPlace<'tcx>>,
                    InputPlace<'tcx>,
                > = sym_ex
                    .arena
                    .mk_synthetic(sym_ex.alloc(PrustiSymValSyntheticData::PureFnCall(
                        def_id,
                        substs,
                        old_map_encoded_args,
                    )));
                let result: FunctionCallResult<
                    'sym,
                    'tcx,
                    PrustiSymValSynthetic<'sym, 'tcx, SymVar>,
                    PrustiSymValSynthetic<'sym, 'tcx, InputPlace<'tcx>>,
                > = FunctionCallResult::Value {
                    value: sym_ex.arena.mk_synthetic(
                        sym_ex
                            .arena
                            .alloc(PrustiSymValSyntheticData::PureFnCall(def_id, substs, args)),
                    ),
                    old_map_value: Some(old_map_value),
                    postcondition: None,
                };
                return Some(FunctionCallEffects {
                    precondition_assertion: None,
                    result,
                    snapshot: None,
                });
            } else {
                return None;
            }
        })
    }

    fn encode_loop_invariant<'heap, 'mir: 'heap>(
        loop_head: mir::BasicBlock,
        mut path: Path<'sym, 'tcx, Self::SymValSynthetic, Self::OldMapSymValSynthetic>,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
    ) -> Vec<(PrustiPathConditions<'sym, 'tcx>, PrustiSymValue<'sym, 'tcx>)> {
        let arena = sym_ex.arena;
        let tcx = sym_ex.tcx;
        let body = sym_ex.body;
        let procedure = Procedure::new(tcx, sym_ex.def_id.into(), body.clone());
        let spec_blocks = get_loop_spec_blocks(&procedure, loop_head);
        for bbi in spec_blocks {
            for (i, stmt) in body[bbi].statements.iter().enumerate() {
                if let mir::StatementKind::Assign(box (
                    _,
                    agg @ mir::Rvalue::Aggregate(
                        agg_kind @ box mir::AggregateKind::Closure(cl_def_id, cl_substs),
                        operands,
                    ),
                )) = &stmt.kind
                {
                    return with_def_spec(|def_spec| {
                        let mut heap = SymbolicHeap::new(&mut path.heap, tcx, body, arena);
                        let loop_spec = def_spec.get_loop_spec(&cl_def_id).unwrap();
                        let encoded = SymPureEnc::encode(
                            arena,
                            SymPureEncTask {
                                kind: PureKind::Closure,
                                parent_def_id: loop_spec.def_id().into(),
                                param_env: tcx.param_env(sym_ex.def_id),
                                substs: cl_substs,
                                caller_def_id: None, // TODO
                            },
                            None,
                        );
                        let captured = &operands
                            .iter()
                            .map(|op| sym_ex.encode_operand(&mut heap, op))
                            .collect::<Vec<_>>();
                        let subst = arena.mk_ref(
                            arena.mk_aggregate(
                                AggregateKind::Rust(*agg_kind.clone(), agg.ty(body, tcx)),
                                arena.alloc_slice(&captured),
                            ),
                            Mutability::Not,
                        );
                        let substs = Substs::singleton(SymVar::nth_input(0), subst);
                        eprintln!(
                            "encoded1 {}",
                            encoded.to_vis_string(Some(tcx), &[], OutputMode::Text)
                        );
                        let encoded = encoded.subst(arena, &substs);
                        // let mut transformer = OldTransformer(
                        //     operands
                        //         .iter()
                        //         .enumerate()
                        //         .flat_map(|(i, op)| {
                        //             let place = op.place().unwrap();
                        //             let t = path.old_map.get(&place.into(), arena)?;
                        //             Some((i, t))
                        //         })
                        //         .collect(),
                        // );
                        eprintln!("old map {:?}", path.old_map);
                        encoded.paths
                    });
                } else {
                    let mut heap = SymbolicHeap::new(&mut path.heap, tcx, body, arena);
                    let rhs = sym_ex.handle_stmt_rhs(&stmt, &mut heap);
                    let mut heap = SymbolicHeap::new(&mut path.heap, tcx, body, arena);
                    sym_ex.handle_stmt_lhs(
                        &stmt,
                        &mut heap,
                        mir::Location {
                            block: bbi,
                            statement_index: i,
                        },
                        rhs,
                    );
                    let structure_encoder = sym_ex.old_map_encoder();
                    match &stmt.kind {
                        mir::StatementKind::Assign(box (place, rvalue)) => {
                            let encoded_place: StructureTerm<
                                'sym,
                                'tcx,
                                Self::OldMapSymValSynthetic,
                            > = <OldMapEncoder<'mir, 'sym, 'tcx> as Encoder<
                                'mir,
                                'sym,
                                'tcx,
                                Self::OldMapSymValSynthetic,
                            >>::encode_rvalue(
                                &structure_encoder, &mut path.old_map, rvalue
                            );
                            path.old_map.insert((*place).into(), encoded_place);
                        }
                        _ => {}
                    }
                }
            }
        }
        vec![]
    }
}

struct OldTransformer<'sym, 'tcx>(
    HashMap<usize, StructureTerm<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx, InputPlace<'tcx>>>>,
);

fn get_loop_spec_blocks(procedure: &Procedure, loop_head: mir::BasicBlock) -> Vec<mir::BasicBlock> {
    let mut res = vec![];
    for bbi in procedure.get_reachable_cfg_blocks() {
        if Some(loop_head) == procedure.get_loop_head(bbi) && procedure.is_spec_block(bbi) {
            res.push(bbi)
        } else {
            // debug!(
            //     "bbi {:?} has head {:?} and 'is spec' is {}",
            //     bbi,
            //     self.loop_encoder.get_loop_head(bbi),
            //     self.procedure.is_spec_block(bbi)
            // );
        }
    }
    res
}

impl SymPureEnc {
    pub fn encode<'sym, 'tcx>(
        arena: &'sym SymExContext<'tcx>,
        task: SymPureEncTask<'tcx>,
        debug_output_dir: Option<String>,
    ) -> SymPureEncResult<'sym, 'tcx> {
        let kind = task.kind;
        let def_id = task.parent_def_id;
        let substs = task.substs;
        let caller_def_id = task.caller_def_id;
        vir::with_vcx(move |vcx| {
            let body = match kind {
                PureKind::Closure => vcx
                    .body_mut()
                    .get_closure_body(def_id, substs, caller_def_id),
                PureKind::Spec => vcx.body_mut().get_spec_body(def_id, substs, caller_def_id),
                PureKind::Pure => vcx
                    .body_mut()
                    .get_pure_fn_body(def_id, substs, caller_def_id),
                PureKind::Constant(_promoted) => todo!(),
            };
            let body = body.body().as_ref().clone();
            let symbolic_execution = symbolic_execution::run_symbolic_execution(SymExParams {
                def_id: def_id.as_local().unwrap(),
                body: &body.body,
                tcx: vcx.tcx(),
                fpcs_analysis: pcs::run_free_pcs(
                    &BodyWithBorrowckFacts {
                        body: body.body.clone(),
                        promoted: body.promoted,
                        borrow_set: body.borrow_set,
                        region_inference_context: body.region_inference_context,
                        location_table: body.location_table,
                        input_facts: body.input_facts,
                        output_facts: body.output_facts,
                    },
                    vcx.tcx(),
                    debug_output_dir.clone(),
                ),
                verifier_semantics: PrustiSemantics(PhantomData),
                arena: &arena,
                debug_output_dir: debug_output_dir.clone(),
                new_symvars_allowed: true, // TODO: false
            });
            // assert_eq!(
            //     symbolic_execution.symvars.len(),
            //     arg_count,
            //     "The symvars for pure {:?} don't correspond to its arguments",
            //     def_id
            // );
            SymPureEncResult {
                paths: symbolic_execution
                    .paths
                    .into_iter()
                    .map(|path| (path.pcs().clone(), path.result().unwrap()))
                    .collect(),
                debug_id: Some(fn_debug_name(def_id, substs)),
            }
        })
    }
}
