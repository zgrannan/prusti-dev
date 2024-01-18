use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, DomainIdent, DomainParamData, ExprData, FunctionIdent,
    KnownArityAny, NullaryArity, PredicateIdent, TypeData, UnaryArity, MethodIdent,
};

use super::{TyOps, predicate::mk_method_assign};

pub struct GenericEnc;

#[derive(Clone, Debug)]
pub enum GenericEncError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncOutputRef<'vir> {
    pub snapshot_param_name: &'vir str,
    pub ref_to_pred: PredicateIdent<'vir, BinaryArity<'vir>>,
    pub ref_to_snap: FunctionIdent<'vir, BinaryArity<'vir>>,
    pub domain_type_name: DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>>,
    pub method_assign: MethodIdent<'vir, BinaryArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for GenericEncOutputRef<'vir> {}

impl<'vir> From<&GenericEncOutputRef<'vir>> for TyOps<'vir> {
    fn from(output_ref: &GenericEncOutputRef<'vir>) -> Self {
        TyOps {
            ty_params: &[],
            ref_to_pred: output_ref.ref_to_pred.as_unknown_arity(),
            ref_to_snap: output_ref.ref_to_snap.as_unknown_arity(),
            snapshot: &SNAPSHOT_PARAM_DOMAIN,
            method_assign: output_ref.method_assign,
        }
    }
}

#[derive(Clone, Debug)]
pub struct GenericEncOutput<'vir> {
    pub snapshot_param: vir::Domain<'vir>,
    pub ref_to_pred: vir::Predicate<'vir>,
    pub domain_type: vir::Domain<'vir>,
    pub ref_to_snap: vir::Function<'vir>,
    pub method_assign: vir::Method<'vir>,
}

pub const TYP_DOMAIN: TypeData<'static> = TypeData::Domain("Type", &[]);
pub const SNAPSHOT_PARAM_DOMAIN: TypeData<'static> = TypeData::Domain("s_Param", &[]);

impl TaskEncoder for GenericEnc {
    task_encoder::encoder_cache!(GenericEnc);

    type TaskDescription<'tcx> = (); // ?

    type OutputRef<'vir> = GenericEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericEncOutput<'vir>;

    type EncodingError = GenericEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[allow(non_snake_case)]
    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
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
        let ref_to_pred =
            PredicateIdent::new("p_Param", BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]));
        let type_domain_ident = DomainIdent::nullary("Type");
        let ref_to_snap = FunctionIdent::new(
            "p_Param_snap",
            BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]),
            &SNAPSHOT_PARAM_DOMAIN,
        );
        let method_assign = MethodIdent::new(
            "assign_p_Param",
            BinaryArity::new(&[&TypeData::Ref, &SNAPSHOT_PARAM_DOMAIN]),
        );


        let output_ref = GenericEncOutputRef {
            snapshot_param_name: "s_Param",
            ref_to_pred,
            domain_type_name: type_domain_ident,
            ref_to_snap,
            method_assign
        };
        deps.emit_output_ref::<Self>(
            *task_key,
            output_ref
        );

        let typ = FunctionIdent::new(
            "typ",
            UnaryArity::new(&[&SNAPSHOT_PARAM_DOMAIN]),
            &TYP_DOMAIN,
        );


        vir::with_vcx(|vcx| {
            let ty_ops: TyOps<'vir> = TyOps {
                ty_params: vcx.alloc_slice(&[vcx.mk_local_decl("t", &TYP_DOMAIN).into()]),
                ref_to_pred: ref_to_pred.as_unknown_arity(),
                ref_to_snap: ref_to_snap.as_unknown_arity(),
                snapshot: &SNAPSHOT_PARAM_DOMAIN,
                method_assign: method_assign,
            };
            let method_assign = mk_method_assign(vcx, &ty_ops);
            let t = vcx.mk_local_ex("t", &TYP_DOMAIN);
            let ref_to_snap = vcx.mk_function(
                "p_Param_snap",
                vir::vir_arg_list! { vcx; self: Ref, t: Type },
                vir::vir_type! { vcx; s_Param },
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr(ref_to_pred.apply(
                    vcx,
                    [vcx.mk_local_ex("self", &TypeData::Ref), t],
                    None,
                ))]),
                vcx.alloc_slice(&[vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    typ.apply(vcx, [vcx.mk_local_ex("result", &SNAPSHOT_PARAM_DOMAIN)]),
                    t,
                )]),
                None,
            );
            Ok((
                GenericEncOutput {
                    method_assign,
                    snapshot_param: vir::vir_domain! { vcx; domain s_Param {
                            function typ(s_Param): Type;
                        }
                    },
                    ref_to_pred: vir::vir_predicate! { vcx; predicate p_Param(self_p: Ref, t: Type) },
                    domain_type: vir::vir_domain! { vcx; domain Type { } },
                    ref_to_snap,
                },
                (),
            ))
        })
    }
}
