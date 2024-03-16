use prusti_rustc_interface::{
    middle::ty::{self, TyKind, util::IntTypeExt, IntTy, UintTy},
    abi,
    span::symbol,
};
use rustc_middle::ty::ParamTy;
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{
    BinaryArity, CallableIdent, DomainParamData, FunctionIdent, NullaryArityAny, ToKnownArity, UnaryArity, UnknownArity
};

/// You probably never want to use this, use `SnapshotEnc` instead.
/// Note: there should never be a dependency on `PredicateEnc` inside this
/// encoder!
pub struct DomainEnc;

#[derive(Clone, Copy, Debug)]
pub struct FieldFunctions<'vir> {
    /// Snapshot of self as argument. Returns domain of field.
    pub read: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Snapshot of self as first argument and of field as second. Returns
    /// updated domain of self.
    pub write: FunctionIdent<'vir, BinaryArity<'vir>>,
}

#[derive(Clone, Copy, Debug)]
pub struct DomainDataPrim<'vir> {
    pub prim_type: vir::Type<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataStruct<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    /// Functions to access the fields.
    pub field_access: &'vir [FieldFunctions<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataEnum<'vir> {
    pub discr_ty: vir::Type<'vir>,
    pub discr_prim: DomainDataPrim<'vir>,
    pub discr_bounds: DiscrBounds<'vir>,
    pub snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [DomainDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataVariant<'vir> {
    pub name: symbol::Symbol,
    pub vid: abi::VariantIdx,
    pub discr: vir::Expr<'vir>,
    pub fields: DomainDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum DiscrBounds<'vir> {
    Range { lower: vir::Expr<'vir>, upper: vir::Expr<'vir> },
    Explicit(&'vir [vir::Expr<'vir>]),
}

#[derive(Clone, Copy, Debug)]
pub enum DomainEncSpecifics<'vir> {
    Param,
    Primitive(DomainDataPrim<'vir>),
    // structs, tuples
    StructLike(DomainDataStruct<'vir>),
    EnumLike(Option<DomainDataEnum<'vir>>),
}

#[derive(Clone, Debug)]
pub struct DomainEncOutputRef<'vir> {
    pub base_name: String,
    pub domain: vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>,
    generic_accessors: &'vir [FunctionIdent<'vir, UnaryArity<'vir>>],
    pub typeof_function: FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl <'vir> DomainEncOutputRef<'vir> {
    pub fn get_typaram_from_snap(
        &self,
        vcx: &'vir vir::VirCtxt,
        idx: usize,
        snap: vir::Expr<'vir>
    ) -> vir::Expr<'vir> {
        self.generic_accessors[idx].apply(
            vcx,
            [self.typeof_function.apply(vcx, [snap])]
        )
    }
}

impl<'vir> task_encoder::OutputRefAny for DomainEncOutputRef<'vir> {}

use crate::encoders::{generic::GenericEncOutputRef, GenericEnc};

use super::{
    generic_cast::{GenericCastEnc, GenericCastOutputRef}, lifted::{LiftedTy, LiftedTyEnc}, lifted_ty_function::LiftedTyFunctionEnc, most_generic_ty::{extract_type_params, MostGenericTy}, rust_ty_snapshots::RustTySnapshotsEnc
};

pub fn all_outputs<'vir>() -> Vec<vir::Domain<'vir>> {
    DomainEnc::all_outputs()
}

impl TaskEncoder for DomainEnc {
    task_encoder::encoder_cache!(DomainEnc);

    type TaskDescription<'vir> = MostGenericTy<'vir>;

    type OutputRef<'vir> = DomainEncOutputRef<'vir>;
    type OutputFullDependency<'vir> = DomainEncSpecifics<'vir>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;
    //type OutputFullDependency<'vir> = DomainEncOutputDep<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
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
            let base_name = task_key.get_vir_base_name(vcx);
            match task_key.kind() {
                TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)  => {
                    let prim_type = match task_key.kind() {
                        TyKind::Bool => &vir::TypeData::Bool,
                        TyKind::Int(_) => &vir::TypeData::Int,
                        TyKind::Uint(_) => &vir::TypeData::Int,
                        _ => todo!(),
                    };

                    let mut enc = DomainEncData::new(vcx, task_key, vec![], deps);
                    enc.deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                    let specifics = enc.mk_prim_specifics(
                        task_key.ty(),
                        prim_type
                    );
                    Ok((enc.finalize(task_key), specifics))
                }
                TyKind::Adt(adt, params) => {
                    let generics =
                        params
                            .iter()
                            .filter_map(|p| p.as_type())
                            .map(|ty| deps.require_local::<LiftedTyEnc>(ty).unwrap().expect_generic())
                            .collect();
                    let mut enc = DomainEncData::new(vcx, task_key, generics, deps);
                    enc.deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                    match adt.adt_kind() {
                        ty::AdtKind::Struct => {
                            let fields = if !adt.is_box() {
                                let variant = adt.non_enum_variant();
                                enc.mk_field_tys(variant, params)
                            } else {
                                // Box special case (this should be replaced by an
                                // extern spec in the future)
                                vec![
                                    FieldTy {
                                        ty: enc.deps.require_ref::<GenericEnc>(()).unwrap().param_snapshot,
                                        lifted: None
                                    }
                                ]
                            };
                            let specifics = enc.mk_struct_specifics(fields);
                            Ok((enc.finalize(task_key), specifics))
                        }
                        ty::AdtKind::Enum => {
                            let variants: Vec<_> = adt.discriminants(vcx.tcx).map(|(v, d)| {
                                let variant = adt.variant(v);
                                let field_tys = enc.mk_field_tys(variant, params);
                                (variant.name, v, field_tys, d)
                            }).collect();
                            let variants = if variants.is_empty() {
                                None
                            } else {
                                let has_explicit = adt
                                    .variants()
                                    .iter()
                                    .any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_)));
                                let discr_ty = adt.repr().discr_type().to_ty(vcx.tcx);
                                let discr_ty = enc.deps
                                    .require_local::<RustTySnapshotsEnc>(discr_ty)
                                    .unwrap()
                                    .generic_snapshot;
                                Some(VariantData {
                                    discr_ty: discr_ty.snapshot,
                                    discr_prim: discr_ty.specifics.expect_primitive(),
                                    has_explicit,
                                    variants,
                                })
                            };
                            let specifics = enc.mk_enum_specifics(variants);
                            Ok((enc.finalize(task_key), specifics))
                        }
                        ty::AdtKind::Union => todo!(),
                    }
                }
                TyKind::Tuple(params) => {
                    let generics = params
                        .iter()
                        .map(|ty| deps.require_local::<LiftedTyEnc>(ty).unwrap().expect_generic())
                        .collect();
                    let mut enc = DomainEncData::new(vcx, task_key, generics, deps);
                    enc.deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                    let field_tys = params.iter().map(|ty| FieldTy::from_ty(vcx, enc.deps, ty)).collect();
                    let specifics = enc.mk_struct_specifics(field_tys);
                    Ok((enc.finalize(task_key), specifics))
                }
                TyKind::Never => {
                    let mut enc = DomainEncData::new(vcx, task_key, vec![], deps);
                    enc.deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                    let specifics = enc.mk_enum_specifics(None);
                    Ok((enc.finalize(task_key), specifics))
                }
                &TyKind::Ref(_, inner, _) => {
                    let generics = vec![deps.require_local::<LiftedTyEnc>(inner).unwrap().expect_generic()];
                    let mut enc = DomainEncData::new(vcx, task_key, generics, deps);
                    enc.deps.emit_output_ref::<Self>(*task_key, enc.output_ref(String::from(base_name)));
                    let field_tys = vec![FieldTy::from_ty(vcx, enc.deps, inner)];
                    let specifics = enc.mk_struct_specifics(field_tys);
                    Ok((enc.finalize(task_key), specifics))
                }
                &TyKind::Param(_) => {
                    let out = deps.require_ref::<GenericEnc>(()).unwrap();
                    deps.emit_output_ref::<Self>(
                        *task_key,
                        DomainEncOutputRef {
                            base_name,
                            domain: out.domain_param_name,
                            generic_accessors: &[],
                            typeof_function: out.param_type_function,
                        },
                    );
                    Ok((
                        deps.require_local::<GenericEnc>(())
                            .map(|enc| enc.param_snapshot)
                            .unwrap(),
                        DomainEncSpecifics::Param,
                    ))
                }
                kind => todo!("{kind:?}"),
            }
        })
    }
}

pub struct VariantData<'vir, 'tcx>  {
    discr_ty: vir::Type<'vir>,
    discr_prim: DomainDataPrim<'vir>,
    /// Do any of the variants have an explicit discriminant value?
    has_explicit: bool,
    variants: Vec<(symbol::Symbol, abi::VariantIdx, Vec<FieldTy<'vir>>, ty::util::Discr<'tcx>)>,
}

struct DomainEncData<'vir, 'tcx, 'enc> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    domain: vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>,
    generics: Vec<(ParamTy, vir::FunctionIdent<'vir, UnaryArity<'vir>>)>,
    typeof_function: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    self_ty: vir::Type<'vir>,
    self_ex: vir::Expr<'vir>,
    self_decl: &'vir [vir::LocalDecl<'vir>; 1],
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
    generic_enc: GenericEncOutputRef<'vir>,
    deps: &'enc mut TaskEncoderDependencies<'vir>,
    is_param_ty: bool
}
impl<'vir, 'tcx: 'vir, 'enc> DomainEncData<'vir, 'tcx, 'enc> {
    // Creation
    fn new(
        vcx: &'vir vir::VirCtxt<'tcx>,
        ty: &MostGenericTy<'tcx>,
        generics: Vec<ParamTy>,
        deps: &'enc mut TaskEncoderDependencies<'vir>,
    ) -> Self {
        let domain = ty.get_vir_domain_ident(vcx);
        let self_ty = domain.apply(vcx, []);

        let self_local = vcx.mk_local("self", self_ty);
        let self_ex = vcx.mk_local_ex_local(self_local);
        let self_decl = vcx.alloc_array(&[vcx.mk_local_decl_local(self_local)]);

        let generic_enc = deps.require_ref::<GenericEnc>(()).unwrap();

        let generic_accessors = deps.require_ref::<LiftedTyFunctionEnc>(*ty).unwrap().inv_functions;
        let generics: Vec<_> = generics.into_iter().zip(generic_accessors.into_iter().map(|t| *t)).collect();

        let mut functions = vec![];

        let typeof_function = if !ty.is_generic() {
            let typeof_function = vir::FunctionIdent::new(
                vir::vir_format!(vcx, "typeof_{}", domain.name()),
                UnaryArity::new(vcx.alloc_array(&[self_ty])),
                generic_enc.type_snapshot
            );
            functions.push(
                vcx.mk_domain_function(typeof_function, false)
            );
            typeof_function
        } else {
            generic_enc.param_type_function
        };

        Self {
            vcx,
            domain,
            self_ty,
            self_ex,
            self_decl,
            generics,
            axioms: Vec::new(),
            functions,
            deps,
            typeof_function,
            generic_enc,
            is_param_ty: ty.is_generic(),
        }
    }


    // Intermediate values
    pub fn mk_field_tys(
        &mut self,
        variant: &ty::VariantDef,
        params: ty::GenericArgsRef<'tcx>,
    ) -> Vec<FieldTy<'vir>> {
        variant
            .fields
            .iter()
            .map(|f| f.ty(self.vcx.tcx, params))
            .map(|ty| FieldTy::from_ty(self.vcx, self.deps, ty))
            .collect()
    }

    // Creating specifics
    pub fn mk_prim_specifics(
        &mut self,
        ty: ty::Ty<'tcx>,
        prim_type: vir::Type<'vir>,
    ) -> DomainEncSpecifics<'vir> {
        let prim_type_args = vec![FieldTy {
                ty: prim_type,
                lifted: None,
        }];
        let data = self.mk_field_functions(
            &prim_type_args,
            None,
            ty.is_integral()
        );
        // TODO: what to do about write?
        let snap_to_prim = data.field_access[0].read;
        let specifics = DomainDataPrim {
            prim_type,
            snap_to_prim,
            prim_to_snap: data.field_snaps_to_snap.to_known(),
        };
        specifics.bounds(ty).map(|(lower, upper)| {
            let exp = snap_to_prim.apply(self.vcx, [self.self_ex]);
            let axiom = self.mk_bounds_axiom(self.domain.name(), exp, lower, upper);
            self.axioms.push(axiom);
        });
        DomainEncSpecifics::Primitive(specifics)
    }
    pub fn mk_struct_specifics(
        &mut self,
        fields: Vec<FieldTy<'vir>>,
    ) -> DomainEncSpecifics<'vir> {
        let specifics = self.mk_field_functions(&fields, None, false);
        DomainEncSpecifics::StructLike(specifics)
    }
    pub fn mk_enum_specifics(
        &mut self,
        data: Option<VariantData<'vir, 'tcx>>,
    ) -> DomainEncSpecifics<'vir> {
        let specifics = data.map(|data| {
            let discr_vals: Vec<_> = data.variants.iter().map(|(_, _, _, discr)| data.discr_prim.expr_from_bits(discr.ty, discr.val)).collect();
            let snap_to_discr_snap = self.mk_discr_function(data.discr_ty);
            let variants = self.vcx.alloc_slice(&data.variants.iter().enumerate().map(|(idx, (name, vid, fields, _))| {
                let discr = (snap_to_discr_snap, data.discr_prim.prim_to_snap.apply(self.vcx, [discr_vals[idx]]), *name);
                let fields = self.mk_field_functions(fields, Some(discr), false);
                DomainDataVariant { name: *name, vid: *vid, discr: discr_vals[idx], fields }
            }).collect::<Vec<_>>());
            let discr_bounds = self.mk_discr_bounds_axioms(data.discr_prim, snap_to_discr_snap, discr_vals, data.has_explicit);
            DomainDataEnum {
                discr_ty: data.discr_ty,
                discr_prim: data.discr_prim,
                discr_bounds,
                snap_to_discr_snap,
                variants,
            }
        });
        DomainEncSpecifics::EnumLike(specifics)
    }

    fn push_function(&mut self, func: FunctionIdent<'vir, UnknownArity<'vir>>, unique: bool) {
        self.functions.push(self.vcx.mk_domain_function(func, unique));
    }

    // Helper functions
    fn mk_field_functions(
        &mut self,
        field_tys: &Vec<FieldTy<'vir>>,
        discr: Option<(FunctionIdent<'vir, UnaryArity<'vir>>, vir::Expr<'vir>, symbol::Symbol)>,
        stronger_cons_axiom: bool,
    ) -> DomainDataStruct<'vir> {
        let name = self.domain.name();
        let base = discr.map(|(_, _, v)| format!("{name}_{v}")).unwrap_or_else(|| name.to_string());
        // Constructor
        let field_snaps_to_snap = {
            let name = vir::vir_format!(self.vcx, "{base}_cons");
            let ident = FunctionIdent::new(
                name,
                UnknownArity::new(self.vcx.alloc_slice(&field_tys.iter().map(|fty| fty.ty).collect::<Vec<_>>())),
                self.self_ty
            );
            self.push_function(ident, false);
            ident
        };

        // Variables and definitions useful for axioms
        let fnames = field_tys.iter().enumerate().map(|(idx, ty)|
            self.vcx.mk_local(vir::vir_format!(self.vcx, "f{idx}"), ty.ty)
        ).collect::<Vec<_>>();
        let cons_qvars: Vec<_> = field_tys.iter().enumerate().map(|(idx, _)|
            self.vcx.mk_local_decl_local(fnames[idx])
        ).collect();
        let cons_qvars = self.vcx.alloc_slice(&cons_qvars);
        let cons_args: Vec<_> = fnames.into_iter().map(|fname| self.vcx.mk_local_ex_local(fname)).collect();
        let cons_call_with_qvars = field_snaps_to_snap.apply(self.vcx, &cons_args);

        // Discriminant axioms
        if let Some((get_discr, val, _)) = discr {
            let discr = get_discr.apply(self.vcx, [cons_call_with_qvars]);
            let mut expr = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, discr, val);
            if !field_tys.is_empty() {
                expr = self.vcx.mk_forall_expr(
                    cons_qvars,
                    self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[discr])]),
                    expr,
                );
            }
            self.axioms.push(self.vcx.mk_domain_axiom(
                vir::vir_format!(self.vcx, "ax_{base}_cons_discr"),
                expr,
            ));
        }

        // Accessors
        let field_access = {
            field_tys.iter().enumerate().map(|(idx, field_ty)| {
                // Read
                let name = vir::vir_format!(self.vcx, "{base}_read_{idx}");
                let args = self.vcx.alloc_array(&[self.self_ty]);
                let read = FunctionIdent::new(
                    name,
                    UnaryArity::new(args),
                    field_ty.ty
                );

                let self_ty = self.typeof_function.apply(self.vcx, [self.self_ex]);
                if let Some(lifted) = &field_ty.lifted {
                    let mut generic_to_getter = |p: ParamTy|
                        self.generics.iter()
                            .find_map(
                                |(g, ident)| if g == &p { Some(ident) } else { None }
                            ).unwrap()
                            .apply(self.vcx, [self_ty]);
                    self.axioms.push(
                        self.vcx.mk_domain_axiom(
                            vir::vir_format!(self.vcx, "ax_{base}_read_{idx}_type"),
                            self.vcx.mk_forall_expr(
                                self.vcx.alloc_slice(self.self_decl),
                                self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[read.apply(self.vcx, [self.self_ex])])]),
                                self.vcx.mk_eq_expr(
                                    self.generic_enc.param_type_function.apply(
                                        self.vcx,
                                        [
                                            lifted.cast_functions.cast_to_generic_if_necessary(
                                                self.vcx,
                                                read.apply(self.vcx, [self.self_ex])
                                            )
                                        ]
                                    ),
                                    lifted.lifted_ty.map(self.vcx, &mut generic_to_getter).expr(self.vcx)
                                )
                            )
                        )
                    );

                }

                self.functions.push(self.vcx.mk_domain_function(read, false));

                let cons_read = read.apply(self.vcx, [cons_call_with_qvars]);
                self.axioms.push(self.vcx.mk_domain_axiom(
                    vir::vir_format!(self.vcx, "ax_{base}_cons_read_{idx}"),
                    self.vcx.mk_forall_expr(
                        cons_qvars,
                        self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[cons_call_with_qvars])]),
                        self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, cons_read, cons_args[idx])
                    )
                ));

                // Write
                let name = vir::vir_format!(self.vcx, "{base}_write_{idx}");
                let args = self.vcx.alloc_array(&[self.self_ty, field_ty.ty]);
                let write = FunctionIdent::new(
                    name,
                    BinaryArity::new(args),
                    self.self_ty
                );
                self.functions.push(self.vcx.mk_domain_function(write, false));
                FieldFunctions { read, write }
            }).collect::<Vec<_>>()
        };

        { // Other axioms
            // TODO: this axiom seems useful even when there are no fields, but
            // I can't figure out which triggers it would have. Is it ok to skip
            // it?
            if !field_access.is_empty() {
                // Constructing from reads leads to same result
                let all_reads: Vec<_> = field_access.iter().map(|field_access| field_access.read.apply(self.vcx, [self.self_ex])).collect();
                let cons_call_with_reads = field_snaps_to_snap.apply(self.vcx, &all_reads);
                let trigger = if stronger_cons_axiom {
                    // Integer types require a simpler trigger to be complete
                    // when snapshot equality may be used on them.
                    assert_eq!(all_reads.len(), 1);
                    all_reads[0]
                } else {
                    cons_call_with_reads
                };
                self.axioms.push(self.vcx.mk_domain_axiom(
                    vir::vir_format!(self.vcx, "ax_{base}_cons"),
                    self.vcx.mk_forall_expr(
                        self.self_decl,
                    self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[trigger])]),
                        self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, cons_call_with_reads, self.self_ex)
                    )
                ));
            };

            // Write and read to different fields change nothing, write and read to
            // the same field sees the new value.
            for (wi, write) in field_access.iter().enumerate() {
                let val_local = self.vcx.mk_local("val", field_tys[wi].ty);
                let val = self.vcx.mk_local_ex_local(val_local);
                let decl = self.vcx.mk_local_decl_local(val_local);
                let write = write.write.apply(self.vcx, [self.self_ex, val]);
                for (ri, read) in field_access.iter().enumerate() {
                    let write_read = read.read.apply(self.vcx, [write]);
                    let rhs = if wi == ri { val } else { read.read.apply(self.vcx, [self.self_ex]) };
                    self.axioms.push(
                        self.vcx.mk_domain_axiom(
                            vir::vir_format!(self.vcx, "ax_{base}_write_{wi}_read_{ri}"),
                            self.vcx.mk_forall_expr(
                                self.vcx.alloc_slice(&[self.self_decl[0], decl]),
                                self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[write_read])]),
                                self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, write_read, rhs)
                            )
                        )
                    );
                }
            }
        }

        DomainDataStruct { field_snaps_to_snap, field_access: self.vcx.alloc_slice(&field_access) }
    }
    fn mk_discr_function(
        &mut self,
        discr_ty: vir::Type<'vir>,
    ) -> FunctionIdent<'vir, UnaryArity<'vir>> {
        let name = vir::vir_format!(self.vcx, "{}_discr", self.domain.name());
        let types = self.vcx.alloc_array(&[self.self_ty]);
        let snap_to_discr_snap = FunctionIdent::new(name, UnaryArity::new(types), discr_ty);
        self.functions
            .push(self.vcx.mk_domain_function(snap_to_discr_snap, false));
        snap_to_discr_snap
    }
    fn mk_discr_bounds_axioms(
        &mut self,
        discr_prim: DomainDataPrim<'vir>,
        snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
        discr_vals: Vec<vir::Expr<'vir>>,
        has_explicit: bool,
    ) -> DiscrBounds<'vir> {
        let discr = snap_to_discr_snap.apply(self.vcx, [self.self_ex]);
        let discr_prim = discr_prim.snap_to_prim.apply(self.vcx, [discr]);
        if has_explicit {
            let discr_vals_eq: Vec<_> = discr_vals.iter().map(|val| self.vcx.mk_eq_expr(discr_prim, *val)).collect();
            let body = self.vcx.mk_disj(&discr_vals_eq);
            self.axioms.push(self.vcx.mk_domain_axiom(
                vir::vir_format!(self.vcx, "{}_discr_values", self.domain.name()),
                self.vcx.mk_forall_expr(
                    self.self_decl,
                    // TODO: should we use `discr` instead of `discr_prim` here?
                    self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[discr_prim])]),
                    body
                )
            ));
            DiscrBounds::Explicit(self.vcx.alloc_slice(&discr_vals))
        } else {
            let base = format!("{}_discr", self.domain.name());
            let lower = discr_vals.first().unwrap();
            let upper = discr_vals.last().unwrap();
            let axiom = self.mk_bounds_axiom(&base, discr_prim, lower, upper);
            self.axioms.push(axiom);
            DiscrBounds::Range { lower, upper }
        }
    }
    fn mk_bounds_axiom(
        &self,
        base: &str,
        exp: vir::Expr<'vir>,
        lower: vir::Expr<'vir>,
        upper: vir::Expr<'vir>,
    ) -> vir::DomainAxiom<'vir> {
        let triggers = self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[exp])]);
        let lower = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, lower, exp);
        let upper = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, exp, upper);
        self.vcx.mk_domain_axiom(vir::vir_format!(self.vcx, "{base}_bounds"), self.vcx.mk_forall_expr(
            self.self_decl,
            triggers,
            self.vcx.mk_bin_op_expr(vir::BinOpKind::And, lower, upper)
        ))
    }

    // Final results
    fn output_ref(
        &self,
        base_name: String,
    ) -> DomainEncOutputRef<'vir> {
        DomainEncOutputRef {
            base_name,
            domain: self.domain,
            typeof_function: self.typeof_function,
            generic_accessors:
                self.vcx.alloc_slice(
                    &self.generics.iter().map(|(_, ident)| *ident).collect::<Vec<_>>()
                ),
        }
    }
    fn finalize(mut self, ty: &MostGenericTy<'tcx>) -> vir::Domain<'vir> {
        if !self.is_param_ty {
            let typeof_applied_to_self = self.typeof_function.apply(self.vcx, [self.self_ex]);
            let generic_cast = self.deps.require_ref::<GenericCastEnc>(*ty).unwrap();
            let as_param = generic_cast.cast_to_generic_if_necessary(self.vcx, self.self_ex);
            self.axioms.push(
                self.vcx.mk_domain_axiom(
                    vir::vir_format!(self.vcx, "ax_typeof_{}", self.domain.name()),
                    self.vcx.mk_forall_expr(
                        self.self_decl,
                        self.vcx.alloc_slice(&[self.vcx.alloc_slice(&[typeof_applied_to_self])]),
                        self.vcx.mk_eq_expr(
                            typeof_applied_to_self,
                            self.generic_enc.param_type_function.apply(self.vcx, [as_param])
                        )
                    )
                )
            );
        }
        self.vcx.mk_domain(
            self.domain.name(),
            &[],
            self.vcx.alloc_slice(&self.axioms),
            self.vcx.alloc_slice(&self.functions),
        )
    }
}

// Utility functions

impl<'vir> DomainEncSpecifics<'vir> {
    pub fn expect_primitive(self) -> DomainDataPrim<'vir> {
        match self {
            Self::Primitive(data) => data,
            _ => panic!("expected primitive"),
        }
    }
    pub fn expect_structlike(self) -> DomainDataStruct<'vir> {
        match self {
            Self::StructLike(data) => data,
            _ => panic!("expected struct-like"),
        }
    }
    pub fn get_enumlike(self) -> Option<Option<DomainDataEnum<'vir>>> {
        match self {
            Self::EnumLike(data) => Some(data),
            _ => None,
        }
    }
    pub fn expect_enumlike(self) -> Option<DomainDataEnum<'vir>> {
        self.get_enumlike().expect("expected enum-like")
    }
}
impl<'vir> DomainDataPrim<'vir> {
    pub fn expr_from_bits<'tcx>(&self, ty: ty::Ty<'tcx>, value: u128) -> vir::Expr<'vir> {
        match *self.prim_type {
            vir::TypeData::Bool => vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0))),
            vir::TypeData::Int => {
                let (bit_width, signed) = match ty.kind() {
                    TyKind::Int(IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u64, true),
                    TyKind::Int(ty) => (ty.bit_width().unwrap(), true),
                    TyKind::Uint(UintTy::Usize) => ((std::mem::size_of::<usize>() * 8) as u64, true),
                    TyKind::Uint(ty) => (ty.bit_width().unwrap(), false),
                    kind => unreachable!("{kind:?}"),
                };
                let size = abi::Size::from_bits(bit_width);
                let negative_value = if signed {
                    let value = size.sign_extend(value) as i128;
                    Some(value).filter(|value| value.is_negative())
                } else {
                    None
                };
                match negative_value {
                    Some(value) => vir::with_vcx(|vcx| {
                        let value = vcx.mk_const_expr(vir::ConstData::Int(value.unsigned_abs()));
                        vcx.mk_unary_op_expr(vir::UnOpKind::Neg, value)
                    }),
                    None =>
                        vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Int(value))),
                }
            },
            ref k => unreachable!("{k:?}"),
        }
    }
    fn bounds<'tcx>(&self, ty: ty::Ty<'tcx>) -> Option<(vir::Expr<'vir>, vir::Expr<'vir>)> {
        match *self.prim_type {
            vir::TypeData::Bool => None,
            ref int@vir::TypeData::Int { .. } => {
                let rust_ty = ty.kind();
                Some(vir::with_vcx(|vcx| (vcx.get_min_int(int, rust_ty), vcx.get_max_int(int, rust_ty))))
            },
            ref k => todo!("{k:?}"),
        }
    }
}

/// Data for encoding field access functions and axioms
#[derive(Clone)]
struct FieldTy<'vir> {
    /// The type of encoded field
    ty: vir::Type<'vir>,

    /// Information about the Rust type, only defined for fields that correspond
    /// to actual Rust types. For example, this will be `None` for a Viper
    /// `Bool` field.
    lifted: Option<LiftedRustTyData<'vir>>
}

#[derive(Clone)]
struct LiftedRustTyData<'vir> {
    /// The representation of the Rust type of the field
    lifted_ty: LiftedTy<'vir, ParamTy>,
    /// Data for casting the field to a generic type
    cast_functions: GenericCastOutputRef<'vir>,
}

impl <'vir> FieldTy<'vir> {
    fn from_ty<'tcx: 'vir>(vcx: &'vir vir::VirCtxt<'tcx>, deps: &mut TaskEncoderDependencies, ty: ty::Ty<'tcx>) -> FieldTy<'vir> {
        let vir_ty = deps.require_local::<RustTySnapshotsEnc>(ty)
            .unwrap()
            .generic_snapshot
            .snapshot;
        let lifted_ty = deps.require_local::<LiftedTyEnc>(ty)
            .unwrap();
        let (generic_ty, _) = extract_type_params(vcx.tcx, ty);
        let cast_functions = deps.require_ref::<GenericCastEnc>(generic_ty).unwrap();
        FieldTy {ty: vir_ty, lifted: Some(LiftedRustTyData {lifted_ty, cast_functions})}
    }
}
