use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{CallableIdent, DomainParamData, FunctionIdent, KnownArityAny, NullaryArityAny, UnaryArity, UnknownArity};

use crate::encoders::{most_generic_ty::extract_type_params, GenericEnc};

use super::most_generic_ty::MostGenericTy;

#[derive(Clone)]
pub struct LiftedTyFunctionEncOutputRef<'vir> {
    /// Takes as input the generics for this type (if any),
    /// and returns the resulting type
    pub function: vir::FunctionIdent<'vir, UnknownArity<'vir>>,

    /// Inv functions
    pub inv_functions: &'vir [vir::FunctionIdent<'vir, UnaryArity<'vir>>],
}

impl<'vir> OutputRefAny for LiftedTyFunctionEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct LiftedTyFunctionEncOutput<'vir> {
    pub domain: vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>,
    pub functions: &'vir [vir::DomainFunction<'vir>],
    pub axioms: &'vir [vir::DomainAxiom<'vir>],
}

pub struct LiftedTyFunctionEnc;

impl TaskEncoder for LiftedTyFunctionEnc {
    task_encoder::encoder_cache!(LiftedTyFunctionEnc);
    type TaskDescription<'tcx> = MostGenericTy<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputRef<'vir> = LiftedTyFunctionEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = LiftedTyFunctionEncOutput<'vir>;

    type OutputFullDependency<'vir> = ();

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
        let mut functions = vec![];
        let mut axioms = vec![];
        vir::with_vcx(|vcx| {
            let (ty_constructor, _) = extract_type_params(vcx.tcx, task_key.ty());
            let args = ty_constructor.generics();
            let type_function_args = vcx.alloc_slice(&vec![generic_ref.type_snapshot; args.len()]);
            let type_function_ident = FunctionIdent::new(
                vir::vir_format!(vcx, "s_{}_type", ty_constructor.get_vir_base_name(vcx)),
                UnknownArity::new(&type_function_args),
                generic_ref.type_snapshot,
            );
            functions.push(vcx.mk_domain_function(
                type_function_ident,
                false,
            ));
            let ty_arg_decls: Vec<vir::LocalDecl<'vir>> = args.iter().enumerate().map(
                |(idx, _)|
                    vcx.mk_local_decl(vcx.alloc_str(&format!("arg_{}", idx)), generic_ref.type_snapshot)
            ).collect();
            let ty_arg_exprs: Vec<vir::Expr<'vir>> = ty_arg_decls.iter().map(|decl| vcx.mk_local_ex(decl.name, decl.ty)).collect::<Vec<_>>();
            let func_app = type_function_ident.apply(vcx, &ty_arg_exprs);

            let inv_function_args = vcx.alloc_array(&[generic_ref.type_snapshot]);
            let inv_functions = args.iter().enumerate().map(|(idx, arg)| {
                FunctionIdent::new(
                    vir::vir_format!(
                        vcx,
                        "s_{}_type_typaram{}",
                        ty_constructor.get_vir_base_name(vcx),
                        arg.name
                    ),
                    UnaryArity::new(inv_function_args),
                    generic_ref.type_snapshot,
                )
            }).collect::<Vec<_>>();
            deps.emit_output_ref::<Self>(*task_key, LiftedTyFunctionEncOutputRef {
                function: type_function_ident,
                inv_functions: vcx.alloc_slice(&inv_functions)
            });

            let axiom_qvars = vcx.alloc_slice(&ty_arg_decls);
            let axiom_triggers = vcx.alloc_slice(&[vcx.alloc_slice(&[func_app])]);
            for (inv_function, ty_arg) in inv_functions.iter().zip(ty_arg_exprs.iter()) {
                functions.push(
                    vcx.mk_domain_function(
                        *inv_function,
                        false,
                    )
                );
                axioms.push(
                    vcx.mk_domain_axiom(
                        vir::vir_format!(vcx, "ax_{}", inv_function.name()),
                        vcx.mk_forall_expr(
                            axiom_qvars,
                            axiom_triggers,
                            vcx.mk_eq_expr(
                                inv_function.apply(vcx, [func_app]),
                                ty_arg
                            )
                        )
                    )
                )
            }
            let result = LiftedTyFunctionEncOutput {
                domain: task_key.get_vir_domain_ident(vcx),
                functions: vcx.alloc_slice(&functions),
                axioms: vcx.alloc_slice(&axioms),
            };
            Ok((result, ()))
        })
    }
}
