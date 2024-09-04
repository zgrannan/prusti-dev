use prusti_rustc_interface::{
    middle::{
        mir::{self, ConstValue},
        ty,
    },
    span::{def_id::DefId, Span}
};
use rustc_middle::mir::interpret::{GlobalAlloc, Scalar};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Arity, CallableIdent};

pub struct ConstEnc;

#[derive(Clone, Debug)]
pub struct ConstEncOutputRef<'vir> {
    pub base_name: String,
    pub snap_inst: vir::Type<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for ConstEncOutputRef<'vir> {}

use crate::encoders::{mir_pure::PureKind, MirPureEnc, MirPureEncTask};

use super::{
    lifted::{casters::CastTypePure, rust_ty_cast::RustTyCastersEnc},
    rust_ty_snapshots::RustTySnapshotsEnc,
};

impl ConstEnc {
    fn encode_const_value<'tcx: 'vir, 'vir: 'tcx>(
        val: ConstValue,
        ty: ty::Ty<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<vir::Expr<'vir>, EncodeFullError<'vir, Self>> {
        let snapshot = deps.require_local::<RustTySnapshotsEnc>(ty)?;
        let kind = snapshot.generic_snapshot.specifics;
        let result = match val {
            ConstValue::Scalar(Scalar::Int(int)) => {
                let prim = kind.expect_primitive();
                let val = int.try_to_bits(int.size()).unwrap();
                let val = prim.expr_from_bits(ty, val);
                vir::with_vcx(|vcx| prim.prim_to_snap.apply(vcx, [val]))
            }
            ConstValue::Scalar(Scalar::Ptr(ptr, _)) => vir::with_vcx(|vcx| {
                match vcx.tcx().global_alloc(ptr.provenance.alloc_id()) {
                    GlobalAlloc::Function(_) => todo!(),
                    GlobalAlloc::VTable(_, _) => todo!(),
                    GlobalAlloc::Static(_) => todo!(),
                    GlobalAlloc::Memory(_mem) => {
                        // If the `unwrap` ever panics we need a different way to get the inner type
                        // let inner_ty = ty.builtin_deref(true).map(|t| t.ty).unwrap_or(ty);
                        let _inner_ty = ty.builtin_deref(true).unwrap();
                        todo!()
                    }
                }
            }),
            ConstValue::ZeroSized => {
                let s = kind.expect_structlike();
                vir::with_vcx(|vcx| {
                    s.field_snaps_to_snap
                        .apply(vcx, snapshot.ty_arg_exprs(vcx), &[])
                })
            }
            // Encode `&str` constants to an opaque domain. If we ever want to perform string reasoning
            // we will need to revisit this encoding, but for the moment this allows assertions to avoid
            // crashing Prusti.
            ConstValue::Slice { .. } if ty.peel_refs().is_str() => {
                let ref_ty = kind.expect_structlike();
                let str_ty = ty.peel_refs();
                let str_snap = deps
                    .require_local::<RustTySnapshotsEnc>(str_ty)?
                    .generic_snapshot
                    .specifics
                    .expect_structlike();
                let cast = deps.require_local::<RustTyCastersEnc<CastTypePure>>(str_ty)?;
                vir::with_vcx(|vcx| {
                    // first, we create a string snapshot
                    let snap = str_snap.field_snaps_to_snap.apply(vcx, &[], &[]);
                    // upcast it to a param
                    let snap = cast.cast_to_generic_if_necessary(vcx, snap);
                    // wrap it in a ref
                    ref_ty
                        .field_snaps_to_snap
                        .apply(vcx, snapshot.ty_arg_exprs(vcx), vec![snap])
                })
            }
            ConstValue::Slice { .. } => todo!("ConstValue::Slice"),
            ConstValue::Indirect { .. } => todo!("ConstValue::Indirect"),
        };
        Ok(result)
    }
}

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);

    type TaskDescription<'vir> = (
        mir::Const<'vir>,
        usize, // current encoding depth
        DefId, // DefId of the current function
    );
    type OutputFullLocal<'vir> = vir::Expr<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (const_, encoding_depth, def_id) = *task_key;
        let res = match const_ {
            mir::Const::Val(val, ty) => Self::encode_const_value(val, ty, deps)?,
            mir::Const::Unevaluated(uneval, ty) => vir::with_vcx(|vcx| match uneval.promoted {
                Some(promoted) => {
                    let task = MirPureEncTask {
                        encoding_depth: encoding_depth + 1,
                        parent_def_id: uneval.def,
                        param_env: vcx.tcx().param_env(uneval.def),
                        substs: ty::List::identity_for_item(vcx.tcx(), uneval.def),
                        kind: PureKind::Constant(promoted),
                        caller_def_id: Some(def_id),
                    };
                    let expr = deps.require_local::<MirPureEnc>(task)?.expr;
                    use vir::Reify;
                    Ok(expr.reify(vcx, (uneval.def, &[])))
                }
                None => {
                    let evaluated = const_
                        .eval(vcx.tcx(), vcx.tcx().param_env(uneval.def), Span::default())
                        .unwrap();
                    Self::encode_const_value(evaluated, ty, deps)
                }
            })?,
            mir::Const::Ty(_) => todo!("ConstantKind::Ty"),
        };
        Ok((res, ()))
    }
}
