use symbolic_execution::{
    value::{Substs, SymVar},
    Assertion,
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};

use crate::encoders::sym_spec::SymSpecEnc;

use super::{
    expr::SymExprEncoder,
    impure::{PrustiAssertion, SymImpureEnc},
};

pub struct AssertionEncoder<'sym, 'tcx, 'vir, 'enc> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    encoder: &'enc SymExprEncoder<'vir, 'sym, 'tcx>,
}

impl<'sym, 'tcx, 'vir, 'enc> AssertionEncoder<'sym, 'tcx, 'vir, 'enc> {
    pub fn new(
        vcx: &'vir vir::VirCtxt<'tcx>,
        encoder: &'enc SymExprEncoder<'vir, 'sym, 'tcx>,
    ) -> Self {
        Self { vcx, encoder }
    }
    pub fn encode_assertion_clauses<'slf, T>(
        &'slf self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        assertion: &PrustiAssertion<'sym, 'tcx>,
    ) -> Result<Vec<vir::Expr<'vir>>, String>
    where
        T: TaskEncoder<EncodingError = String>,
    {
        let arena = self.encoder.arena;
        match assertion {
            Assertion::Value(val) => Ok(vec![self
                .encoder
                .encode_sym_value_as_prim(deps, val, false)
                .unwrap()]),
            Assertion::Precondition(def_id, substs, args) => {
                let arg_substs = arena.alloc(Substs::from_iter(
                    args.iter()
                        .copied()
                        .enumerate()
                        .map(|(i, v)| (SymVar::nth_input(i), v)),
                ));
                let encoded_pres = deps
                    .require_local::<SymSpecEnc>((*def_id, substs, None))
                    .unwrap()
                    .pres
                    .into_iter()
                    .map(|p| {
                        self.encoder
                            .encode_pure_spec(deps, p.subst(arena, arg_substs))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(encoded_pres.into_iter().flat_map(|e| e.clauses).collect())
            }
            Assertion::Implication(lhs, rhs) => {
                let lhs_clauses = self.vcx.mk_conj(&self.encode_assertion_clauses(deps, lhs)?);
                let rhs_clauses = self.vcx.mk_conj(&self.encode_assertion_clauses(deps, rhs)?);
                Ok(vec![self.vcx.mk_implies_expr(lhs_clauses, rhs_clauses)])
            }
            Assertion::PathConditions(conditions) => Ok(self
                .encoder
                .encode_path_condition(deps, conditions)
                .into_iter()
                .flat_map(|pc| pc.atoms)
                .map(|atom| atom.to_expr(self.vcx))
                .collect()),
        }
    }

    pub fn encode_assertion<'slf, T>(
        &'slf self,
        deps: &'enc mut TaskEncoderDependencies<'vir, T>,
        assertion: &PrustiAssertion<'sym, 'tcx>,
    ) -> Vec<vir::Stmt<'vir>>
    where
        T: TaskEncoder<EncodingError = String>,
    {
        match assertion {
            Assertion::Implication(lhs, rhs) => {
                let lhs_clauses = self
                    .vcx
                    .mk_conj(&self.encode_assertion_clauses(deps, lhs).unwrap());
                vec![self.vcx.mk_if_stmt(
                    lhs_clauses,
                    self.vcx.alloc_slice(&self.encode_assertion(deps, rhs)),
                    &[],
                )]
            }
            _ => match self.encode_assertion_clauses(deps, assertion) {
                Ok(clauses) => clauses
                    .into_iter()
                    .map(|expr| self.vcx.mk_exhale_stmt(expr))
                    .collect(),
                Err(err) => vec![
                    self.vcx.mk_comment_stmt(self.vcx.alloc(err)),
                    self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false, !, !>()),
                ],
            },
        }
    }
}
