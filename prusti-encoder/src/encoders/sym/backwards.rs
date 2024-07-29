use std::collections::BTreeMap;
use symbolic_execution::results::SymbolicExecutionResult;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{Method, UnknownArity, ViperIdent};

use crate::encoders::{sym_impure::ForwardBackwardsShared, sym_pure::PrustiSymValSynthetic};

use super::expr::SymExprEncoder;

pub fn mk_backwards_method<'enc, 'vir, 'sym, 'tcx, T: TaskEncoder<EncodingError = String>>(
    base_method_name: ViperIdent<'vir>,
    mut fb_shared: ForwardBackwardsShared<'vir>,
    deps: &'enc mut TaskEncoderDependencies<'vir, T>,
    encoder: SymExprEncoder<'vir, 'sym, 'tcx>,
    sym_ex_results: &SymbolicExecutionResult<'sym, 'tcx, PrustiSymValSynthetic<'sym, 'tcx>>,
) -> vir::Method<'vir> {
    vir::with_vcx(|vcx| {
        // The map from an index in `BackwardsFact` to the backwards result local
        let mut back_result_vars: BTreeMap<usize, vir::Expr<'vir>> = BTreeMap::default();

        // Get the local for the back result for a given index in `BackwardsFact`
        let mut get_back_result = |idx| {
            if !back_result_vars.contains_key(&idx) {
                let name = vir::vir_format!(vcx, "backwards_{}", idx);
                let ty = fb_shared.symvar_locals[idx].ty;
                fb_shared
                    .decl_stmts
                    .push(vcx.mk_local_decl_stmt(vcx.mk_local_decl(name, ty), None));
                back_result_vars.insert(idx, vcx.mk_local_ex(name, ty));
            }
            back_result_vars.get(&idx).unwrap().clone()
        };

        let mut body_stmts = vec![];
        for path in sym_ex_results.paths.iter() {
            let mut path_stmts = vec![];
            for (idx, expr) in path.backwards_facts.0.iter() {
                let expr = encoder.encode_sym_value(deps, expr).unwrap();
                let result_local = get_back_result(*idx);
                path_stmts.push(vcx.mk_inhale_stmt(vcx.mk_eq_expr(result_local, expr)));
            }
            match encoder.encode_path_condition(deps, &path.pcs) {
                Some(condition) => {
                    body_stmts.push(vcx.mk_if_stmt(
                        condition.unwrap(),
                        vcx.alloc_slice(&path_stmts),
                        &[],
                    ));
                }
                None => {
                    body_stmts.extend(path_stmts);
                }
            }
        }
        let method_name = vir::vir_format_identifier!(vcx, "{}_backwards", base_method_name);
        let method_ident = vir::MethodIdent::new(method_name, UnknownArity::new(&[]));
        let mut stmts = fb_shared.decl_stmts;
        stmts.extend(fb_shared.type_assertion_stmts);
        stmts.extend(body_stmts);
        vcx.mk_method(
            method_ident,
            &[],
            &[],
            &[],
            &[],
            Some(vcx.alloc_slice(&[vcx.mk_cfg_block(
                &vir::CfgBlockLabelData::Start,
                vcx.alloc_slice(&stmts),
                &vir::TerminatorStmtGenData::Exit,
            )])),
        )
    })
}
