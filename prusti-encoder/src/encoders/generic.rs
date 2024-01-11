use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, DomainIdent, ExprData, FunctionIdent, NullaryArity, PredicateIdent,
    TypeData, UnaryArity,
};

pub struct GenericEnc;

#[derive(Clone, Debug)]
pub enum GenericEncError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncOutputRef<'vir> {
    pub snapshot_param_name: &'vir str,
    pub param_predicate: PredicateIdent<'vir, BinaryArity<'vir>>,
    pub domain_type_name: DomainIdent<'vir, NullaryArity<'vir>>
}
impl<'vir> task_encoder::OutputRefAny for GenericEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct GenericEncOutput<'vir> {
    pub snapshot_param: vir::Domain<'vir>,
    pub predicate_param: vir::Predicate<'vir>,
    pub domain_type: vir::Domain<'vir>,
    pub param_to_snap: vir::Function<'vir>,
}

pub const TYP_DOMAIN: TypeData<'static> = TypeData::Domain("Type", &[]);

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
        let param_predicate =
            PredicateIdent::new("p_Param", BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]));
        let type_domain_ident = DomainIdent::new("Type", NullaryArity::new(&[]));
        deps.emit_output_ref::<Self>(
            *task_key,
            GenericEncOutputRef {
                snapshot_param_name: "s_Param",
                param_predicate,
                domain_type_name: type_domain_ident
            },
        );
        let typ = FunctionIdent::new("typ", UnaryArity::new(&[&TYP_DOMAIN]));
        vir::with_vcx(|vcx| {
            let t = vcx.mk_local_ex("t");
            let param_snapshot = vcx.mk_function(
                "p_Param_snap",
                vir::vir_arg_list! { vcx; self: Ref, t: Type },
                vir::vir_type! { vcx; s_Param },
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr(param_predicate.apply(
                    vcx,
                    [vcx.mk_local_ex("self"), t],
                    None,
                ))]),
                vcx.alloc_slice(&[vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    typ.apply(vcx, [vcx.mk_local_ex("result")]),
                    t,
                )]),
                None,
            );
            Ok((
                GenericEncOutput {
                    snapshot_param: vir::vir_domain! { vcx; domain s_Param {
                            function typ(s_Param): Type;
                        }
                    },
                    predicate_param: vir::vir_predicate! { vcx; predicate p_Param(self_p: Ref, t: Type) },
                    domain_type: vir::vir_domain! { vcx; domain s_Type { } },
                    param_to_snap: param_snapshot,
                },
                (),
            ))
        })
    }
}
