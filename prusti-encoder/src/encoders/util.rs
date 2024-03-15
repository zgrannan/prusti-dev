use vir::VirCtxt;
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};

/// Returns input and output types of a function
pub fn get_func_sig<'tcx>(vcx: &VirCtxt<'tcx>, def_id: DefId) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>) {
    if let Some(local_def_id) = def_id.as_local() {
        let body = vcx
            .body
            .borrow_mut()
            .get_impure_fn_body_identity(local_def_id);
        let arg_tys = (1..body.arg_count + 1)
            .map(|arg| body.local_decls[arg.into()].ty)
            .collect::<Vec<_>>();
        let result_ty = body.local_decls[mir::RETURN_PLACE].ty;
        (arg_tys, result_ty)
    } else {
        let sig = vcx.tcx.fn_sig(def_id);
        let arg_tys = sig
            .skip_binder()
            .inputs()
            .iter()
            .map(|i| i.skip_binder())
            .copied()
            .collect::<Vec<_>>();
        let result_ty = sig.skip_binder().output().skip_binder();
        (arg_tys, result_ty)
    }
}
