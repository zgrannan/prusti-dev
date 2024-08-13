use prusti_rustc_interface::{
    abi,
    middle::{
        mir::{self, interpret::Scalar, ConstantKind, ProjectionElem},
        ty::{self, GenericArgs, TyKind},
    },
    span::def_id::{DefId, LocalDefId},
};
use symbolic_execution::{
    value::BackwardsFn,
    visualization::{OutputMode, VisFormat},
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{
    lifted::{
        cast::{CastArgs, CastToEnc},
        casters::CastTypePure,
        func_app_ty_params::LiftedFuncAppTyParamsEnc,
    },
    sym_pure::{PrustiSymValSynthetic, PrustiSymValue},
    FunctionCallTaskDescription, SymFunctionEnc, SymImpureEnc,
};

use super::{EncodeSymValueResult, SymExprEncoder};

impl<'vir, 'sym, 'tcx> SymExprEncoder<'vir, 'sym, 'tcx> {
    pub fn encode_backwards_fn_call<'enc, T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        backwards_fn: &BackwardsFn<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
    ) -> EncodeSymValueResult<'vir, String>
    where
        T: 'vir,
    {
        let output_ref = deps
            .require_ref::<SymImpureEnc>((
                backwards_fn.def_id.as_local().unwrap(),
                backwards_fn.substs,
                backwards_fn.caller_def_id,
            ))
            .unwrap();
        let back_fn = &output_ref.backwards_fns[&backwards_fn.arg_index];
        let mono = cfg!(feature = "mono_function_encoding");
        let ty_args = deps
            .require_local::<LiftedFuncAppTyParamsEnc>((mono, backwards_fn.substs))
            .unwrap()
            .into_iter()
            .map(|ty| ty.expr(self.vcx))
            .collect::<Vec<_>>();
        let encoded_args = backwards_fn
            .arg_snapshots
            .iter()
            .copied()
            .chain(std::iter::once(backwards_fn.return_snapshot))
            .map(|arg| self.encode_sym_value(deps, arg))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(back_fn.apply(ty_args, encoded_args))
    }
    pub fn encode_fn_call<'enc, T: TaskEncoder<EncodingError = String>>(
        &self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        fn_def_id: DefId,
        substs: &'tcx GenericArgs<'tcx>,
        args: &[PrustiSymValue<'sym, 'tcx>],
    ) -> EncodeSymValueResult<'vir, String>
    where
        T: 'vir,
    {
        let mono = cfg!(feature = "mono_function_encoding");
        let sig = self.vcx.tcx().fn_sig(fn_def_id);
        let sig = if mono {
            let param_env = self.vcx.tcx().param_env(self.def_id);
            self.vcx
                .tcx()
                .subst_and_normalize_erasing_regions(substs, param_env, sig)
        } else {
            sig.instantiate_identity()
        };

        let fn_arg_tys = sig
            .inputs()
            .iter()
            .map(|i| i.skip_binder())
            .copied()
            .collect::<Vec<_>>();
        let encoded_ty_args = deps
            .require_local::<LiftedFuncAppTyParamsEnc>((mono, substs))
            .unwrap();
        let encoded_args = encoded_ty_args.iter().map(|ty| ty.expr(self.vcx));
        let encoded_fn_args = fn_arg_tys
            .into_iter()
            .zip(args.iter())
            .map(|(expected_ty, arg)| {
                let base = self
                    .encode_sym_value(deps, arg)
                    .map_err(|e| EncodeFullError::EncodingError(e, None))?;
                let arg_ty = arg.ty(self.vcx.tcx()).rust_ty();
                let caster = deps
                    .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                        expected: expected_ty,
                        actual: arg_ty,
                    })
                    .unwrap();
                let result: EncodeSymValueResult<'vir, EncodeFullError<'vir, T>> =
                    Ok(caster.apply_cast_if_necessary(self.vcx, base));
                result
            })
            .collect::<Result<Vec<_>, EncodeFullError<'vir, T>>>()
            .map_err(|e| format!("{:?}", e))?;
        let args = encoded_args.chain(encoded_fn_args).collect::<Vec<_>>();
        let function_ref = deps
            .require_ref::<SymFunctionEnc>(FunctionCallTaskDescription {
                def_id: fn_def_id,
                substs: if mono {
                    substs
                } else {
                    GenericArgs::identity_for_item(self.vcx.tcx(), fn_def_id)
                },
                caller_def_id: self.def_id,
            })
            .map_err(|e| format!("{:?}", e))?
            .function_ident;
        Ok(function_ref.apply(self.vcx, &args))
    }
}
