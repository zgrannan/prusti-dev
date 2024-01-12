use prusti_rustc_interface::{
    middle::ty,
    middle::mir,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{UnknownArity, FunctionIdent, CallableIdent};

pub struct MirBuiltinEnc;

#[derive(Clone, Debug)]
pub enum MirBuiltinEncError {
    Unsupported,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum MirBuiltinEncTask<'tcx> {
    UnOp(ty::Ty<'tcx>, mir::UnOp, ty::Ty<'tcx>),
    BinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
    CheckedBinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncOutputRef<'vir> {
    pub function: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirBuiltinEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncOutput<'vir> {
    pub function: vir::Function<'vir>,
}

use crate::encoders::SnapshotEnc;

impl TaskEncoder for MirBuiltinEnc {
    task_encoder::encoder_cache!(MirBuiltinEnc);

    type TaskDescription<'vir> = MirBuiltinEncTask<'vir>;

    type OutputRef<'vir> = MirBuiltinEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirBuiltinEncOutput<'vir>;

    type EncodingError = MirBuiltinEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        vir::with_vcx(|vcx| {
            match *task_key {
                MirBuiltinEncTask::UnOp(res_ty, op, operand_ty) => {
                    assert_eq!(res_ty, operand_ty);
                    let function = Self::handle_un_op(vcx, deps, *task_key, op, operand_ty);
                    Ok((MirBuiltinEncOutput { function }, ()))
                }
                MirBuiltinEncTask::BinOp(res_ty, op, l_ty, r_ty) => {
                    let function = Self::handle_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty);
                    Ok((MirBuiltinEncOutput { function }, ()))
                }
                MirBuiltinEncTask::CheckedBinOp(res_ty, op, l_ty, r_ty) => {
                    let function = Self::handle_checked_bin_op(vcx, deps, *task_key, res_ty, op, l_ty, r_ty);
                    Ok((MirBuiltinEncOutput { function }, ()))
                }
            }
        })
    }
}

// TODO: this function is also useful for the type encoder, extract?
fn int_name<'tcx>(ty: ty::Ty<'tcx>) -> &'static str {
    match ty.kind() {
        ty::TyKind::Bool => "bool",
        ty::TyKind::Int(kind) => kind.name_str(),
        ty::TyKind::Uint(kind) => kind.name_str(),
        _ => unreachable!("non-integer type"),
    }
}

impl MirBuiltinEnc {
    fn handle_un_op<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        key: <Self as TaskEncoder>::TaskKey<'tcx>,
        op: mir::UnOp,
        ty: ty::Ty<'tcx>
    ) -> vir::Function<'vir> {
        let e_ty = deps.require_local::<SnapshotEnc>(ty).unwrap();

        let name = vir::vir_format!(vcx, "mir_unop_{op:?}_{}", int_name(ty));
        let arity = UnknownArity::new(vcx.alloc_slice(&[e_ty.snapshot]));
        let function = FunctionIdent::new(name, arity);
        deps.emit_output_ref::<Self>(key, MirBuiltinEncOutputRef {
            function,
        });

        let prim_res_ty = e_ty.specifics.expect_primitive();
        let snap_arg = vcx.mk_local_ex("arg", e_ty.snapshot);
        let prim_arg = prim_res_ty.snap_to_prim.apply(vcx, [snap_arg]);
        let mut val = prim_res_ty.prim_to_snap.apply(vcx,
            [vcx.mk_unary_op_expr(vir::UnOpKind::from(op), prim_arg)]
        );
        // Can overflow when doing `- iN::MIN -> iN::MIN`. There is no
        // `CheckedUnOp`, instead the compiler puts an `TerminatorKind::Assert`
        // before in debug mode. We should still produce the correct result in
        // release mode, which the code under this branch does.
        if op == mir::UnOp::Neg && ty.is_signed() {
            let bound = vcx.get_min_int(prim_res_ty.prim_type, ty.kind());
            // `snap_to_prim(arg) == -iN::MIN`
            let cond = vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, prim_arg, bound);
            // `snap_to_prim(arg) == -iN::MIN ? arg :
            // prim_to_snap(-snap_to_prim(arg))`
            val = vcx.mk_ternary_expr(cond, snap_arg, val)
        }

        vcx.mk_function(
            name,
            vcx.alloc_slice(&[vcx.mk_local_decl("arg", e_ty.snapshot)]),
            e_ty.snapshot,
            &[],
            &[],
            Some(val)
        )
    }

    fn handle_bin_op<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        key: <Self as TaskEncoder>::TaskKey<'tcx>,
        res_ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        l_ty: ty::Ty<'tcx>,
        r_ty: ty::Ty<'tcx>,
    ) -> vir::Function<'vir> {
        use mir::BinOp::*;
        let e_l_ty = deps.require_local::<SnapshotEnc>(l_ty).unwrap();
        let e_r_ty = deps.require_local::<SnapshotEnc>(r_ty).unwrap();
        let e_res_ty = deps.require_local::<SnapshotEnc>(res_ty).unwrap();
        let prim_l_ty = e_l_ty.specifics.expect_primitive();
        let prim_r_ty = e_r_ty.specifics.expect_primitive();
        let prim_res_ty = e_res_ty.specifics.expect_primitive();

        let name = vir::vir_format!(vcx, "mir_binop_{op:?}_{}_{}", int_name(l_ty), int_name(r_ty));
        let arity = UnknownArity::new(vcx.alloc_slice(&[e_l_ty.snapshot, e_r_ty.snapshot]));
        let function = FunctionIdent::new(name, arity);
        deps.emit_output_ref::<Self>(key, MirBuiltinEncOutputRef {
            function,
        });
        let lhs = prim_l_ty.snap_to_prim.apply(vcx,
            [vcx.mk_local_ex("arg1", e_l_ty.snapshot)],
        );
        let mut rhs = prim_r_ty.snap_to_prim.apply(vcx,
            [vcx.mk_local_ex("arg2", e_r_ty.snapshot)],
        );
        if matches!(op, Shl | Shr) {
            // RHS must be smaller than the bit width of the LHS, this is
            // implicit in the `Shl` and `Shr` operators.
            rhs = vcx.mk_bin_op_expr(vir::BinOpKind::Mod, rhs, vcx.get_bit_width_int(prim_l_ty.prim_type, l_ty.kind()));
        }
        let val = prim_res_ty.prim_to_snap.apply(vcx,
            [vcx.mk_bin_op_expr(vir::BinOpKind::from(op), lhs, rhs)]
        );
        let (pres, val) = match op {
            // Overflow well defined as wrapping (implicit) and for the shifts
            // the RHS will be masked to the bit width.
            Add | Sub | Mul | Shl | Shr =>
                (Vec::new(), Self::get_wrapped_val(vcx, val, prim_res_ty.prim_type, res_ty)),
            // Undefined behavior to overflow (need precondition)
            AddUnchecked | SubUnchecked | MulUnchecked => {
                let min = vcx.get_min_int(prim_res_ty.prim_type, res_ty.kind());
                // `(arg1 op arg2) >= -iN::MIN`
                let lower_bound = vcx.mk_bin_op_expr(vir::BinOpKind::CmpGe, val, min);
                let max = vcx.get_max_int(prim_res_ty.prim_type, res_ty.kind());
                // `(arg1 op arg2) <= iN::MAX`
                let upper_bound = vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, val, max);
                (vec![lower_bound, upper_bound], val)
            }
            // Overflow is well defined as wrapping (implicit), but shifting by
            // more than the bit width (or less than 0) is undefined behavior.
            ShlUnchecked | ShrUnchecked => {
                let min = vcx.mk_int::<0>();
                // `arg2 >= 0`
                let lower_bound = vcx.mk_bin_op_expr(vir::BinOpKind::CmpGe, rhs, min);
                let max = vcx.get_bit_width_int(prim_l_ty.prim_type, l_ty.kind());
                // `arg2 < bit_width(arg1)`
                let upper_bound = vcx.mk_bin_op_expr(vir::BinOpKind::CmpLt, rhs, max);
                (vec![lower_bound, upper_bound], Self::get_wrapped_val(vcx, val, prim_res_ty.prim_type, res_ty))
            }
            // Could divide by zero or overflow if divisor is `-1`
            Div | Rem => {
                // `0 != arg2 `
                let pre = vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, vcx.mk_int::<0>(), rhs);
                let mut pres = vec![pre];
                if res_ty.is_signed() {
                    let min = vcx.get_min_int(prim_res_ty.prim_type, res_ty.kind());
                    // `arg1 != -iN::MIN`
                    let arg1_cond = vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, lhs, min);
                    // `-1 != arg2 `
                    let arg2_cond = vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, vcx.mk_int::<-1>(), rhs);
                    // `-1 != arg2 || arg1 != -iN::MIN`
                    let pre = vcx.mk_bin_op_expr(vir::BinOpKind::Or, arg1_cond, arg2_cond);
                    pres.push(pre);
                }
                (pres, val)
            }
            // Cannot overflow and no undefined behavior
            BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt | Offset =>
                (Vec::new(), val),
        };
        vcx.mk_function(name,
            vcx.alloc_slice(&[
                vcx.mk_local_decl("arg1", e_l_ty.snapshot),
                vcx.mk_local_decl("arg2", e_r_ty.snapshot),
            ]),
            e_res_ty.snapshot,
            vcx.alloc_slice(&pres),
            &[],
            Some(val)
        )
    }

    fn handle_checked_bin_op<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        key: <Self as TaskEncoder>::TaskKey<'tcx>,
        res_ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        l_ty: ty::Ty<'tcx>,
        r_ty: ty::Ty<'tcx>,
    ) -> vir::Function<'vir> {
        // `op` can only be `Add`, `Sub` or `Mul`
        assert!(matches!(op, mir::BinOp::Add | mir::BinOp::Sub | mir::BinOp::Mul));
        let e_l_ty = deps.require_local::<SnapshotEnc>(l_ty).unwrap();
        let e_r_ty = deps.require_local::<SnapshotEnc>(r_ty).unwrap();

        let name = vir::vir_format!(vcx, "mir_checkedbinop_{op:?}_{}_{}", int_name(l_ty), int_name(r_ty));
        let arity = UnknownArity::new(vcx.alloc_slice(&[e_l_ty.snapshot, e_r_ty.snapshot]));
        let function = FunctionIdent::new(name, arity);
        deps.emit_output_ref::<Self>(key, MirBuiltinEncOutputRef {
            function,
        });

        let e_res_ty = deps.require_local::<SnapshotEnc>(res_ty).unwrap();
        // The result of a checked add will always be `(T, bool)`, get the `T`
        // type
        let rvalue_pure_ty = res_ty.tuple_fields()[0];
        let bool_ty = res_ty.tuple_fields()[1];
        assert!(bool_ty.is_bool());

        let e_rvalue_pure_ty = deps.require_local::<SnapshotEnc>(rvalue_pure_ty).unwrap();
        let e_rvalue_pure_ty = e_rvalue_pure_ty.specifics.expect_primitive();
        let e_bool = deps.require_local::<SnapshotEnc>(bool_ty).unwrap();
        let bool_cons = e_bool.specifics.expect_primitive().prim_to_snap;

        // Unbounded value
        let val_exp = vcx.mk_bin_op_expr(vir::BinOpKind::from(op), e_l_ty.specifics.expect_primitive().snap_to_prim.apply(vcx,
            [vcx.mk_local_ex("arg1", e_l_ty.snapshot)],
        ), e_r_ty.specifics.expect_primitive().snap_to_prim.apply(vcx,
            [vcx.mk_local_ex("arg2", e_r_ty.snapshot)],
        ));
        let val_str = vir::vir_format!(vcx, "val");
        let val = vcx.mk_local_ex(val_str, e_rvalue_pure_ty.prim_type);
        // Wrapped value
        let wrapped_val_exp = Self::get_wrapped_val(vcx, val, e_rvalue_pure_ty.prim_type, rvalue_pure_ty);
        let wrapped_val_str = vir::vir_format!(vcx, "wrapped_val");
        let wrapped_val = vcx.mk_local_ex(wrapped_val_str, e_rvalue_pure_ty.prim_type);
        let wrapped_val_snap = e_rvalue_pure_ty.prim_to_snap.apply(vcx,
            [wrapped_val],
        );
        // Overflowed?
        let overflowed = vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, wrapped_val, val);
        let overflowed_snap = bool_cons.apply(vcx, [overflowed]);
        // `tuple(prim_to_snap(wrapped_val), wrapped_val != val)`
        let tuple = e_res_ty.specifics.expect_structlike().field_snaps_to_snap.apply(vcx,
            &[wrapped_val_snap, overflowed_snap]
        );
        // `let wrapped_val == (val ..) in $tuple`
        let inner_let = vcx.mk_let_expr(wrapped_val_str, wrapped_val_exp, tuple);

        vcx.mk_function(
            name,
            vcx.alloc_slice(&[
                vcx.mk_local_decl("arg1", e_l_ty.snapshot),
                vcx.mk_local_decl("arg2", e_r_ty.snapshot),
            ]),
            e_res_ty.snapshot,
            &[],
            &[],
            Some(vcx.mk_let_expr(val_str, val_exp, inner_let))
        )
    }

    /// Wrap the value in the range of the type, e.g. `uN` is wrapped in the
    /// range `uN::MIN..=uN::MAX` using modulo. For signed integers, the range
    /// is `iN::MIN..=iN::MAX` and the value is wrapped using two's complement.
    fn get_wrapped_val<'vir, 'tcx>(vcx: &'vir vir::VirCtxt<'tcx>, mut exp: &'vir vir::ExprData<'vir>, ty: vir::Type, rust_ty: ty::Ty) -> &'vir vir::ExprData<'vir> {
        let shift_amount = vcx.get_signed_shift_int(ty, rust_ty.kind());
        if let Some(half) = shift_amount {
            exp = vcx.mk_bin_op_expr(vir::BinOpKind::Add, exp, half);
        }
        let modulo_val = vcx.get_modulo_int(ty, rust_ty.kind());
        exp = vcx.mk_bin_op_expr(vir::BinOpKind::Mod, exp, modulo_val);
        if let Some(half) = shift_amount {
            exp = vcx.mk_bin_op_expr(vir::BinOpKind::Sub, exp, half);
        }
        exp
    }
}
