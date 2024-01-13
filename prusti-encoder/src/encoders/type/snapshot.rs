use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};

/// Takes a Rust `Ty` and returns a Viper `Type`. The returned type is always a
/// domain type. To get specifics such as constructors for the domain, use the
/// full encoding: this is generally the one to use as it also includes the type.
pub struct SnapshotEnc;

#[derive(Clone, Debug)]
pub struct SnapshotEncOutputRef<'vir> {
    pub snapshot: vir::Type<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for SnapshotEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct SnapshotEncOutput<'vir> {
    pub base_name: String,
    pub snapshot: vir::Type<'vir>,
    pub specifics: DomainEncSpecifics<'vir>,
}

use crate::util::to_placeholder;

use super::domain::{DomainEnc, DomainEncSpecifics};

impl TaskEncoder for SnapshotEnc {
    task_encoder::encoder_cache!(SnapshotEnc);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;
    type OutputRef<'vir> = SnapshotEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = SnapshotEncOutput<'vir>;
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
            // Here we need to normalise the task description.
            // In particular, any concrete type parameter instantiation is replaced
            // with the identity substitutions for the item.
            // For example:
            //     Assuming `struct Foo<T, U> { .. }`,
            //     `Foo<i32, bool>` is normalised to `Foo<T, U>`
            let (ty, args) = match *task_key.kind() {
                TyKind::Adt(adt, args) => {
                    // TODO: Also encode nested
                    let id = ty::List::identity_for_item(vcx.tcx, adt.did()).iter();
                    let id = vcx.tcx.mk_args_from_iter(id);
                    let ty = vcx.tcx.mk_ty_from_kind(TyKind::Adt(adt, id));
                    (ty, args.into_iter().flat_map(ty::GenericArg::as_type).collect())
                }
                TyKind::Tuple(tys) => {
                    let new_tys = vcx.tcx.mk_type_list_from_iter((0..tys.len()).map(|index|
                        to_placeholder(vcx.tcx, Some(index))
                    ));
                    let ty = vcx.tcx.mk_ty_from_kind(TyKind::Tuple(new_tys));
                    (ty, tys.to_vec())
                }
                TyKind::Array(orig, val) => {
                    let ty = to_placeholder(vcx.tcx, None);
                    let ty = vcx.tcx.mk_ty_from_kind(TyKind::Array(ty, val));
                    (ty, vec![orig])
                }
                TyKind::Slice(orig) => {
                    let ty = to_placeholder(vcx.tcx, None);
                    let ty = vcx.tcx.mk_ty_from_kind(TyKind::Slice(ty));
                    (ty, vec![orig])
                }
                TyKind::Ref(r, orig, m) => {
                    let ty = to_placeholder(vcx.tcx, None);
                    let ty = vcx.tcx.mk_ty_from_kind(TyKind::Ref(r, ty, m));
                    (ty, vec![orig])
                }
                _ => (*task_key, Vec::new()),
            };
            let out = deps.require_ref::<DomainEnc>(ty).unwrap();
            let tys: Vec<_> = args.iter().map(|arg| deps.require_ref::<Self>(*arg).unwrap().snapshot).collect();
            let snapshot = out.domain.apply(vcx, &tys);
            deps.emit_output_ref::<Self>(*task_key, SnapshotEncOutputRef { snapshot });

            let mut names = vec![out.base_name];
            for arg in args {
                let arg = deps.require_local::<Self>(arg).unwrap();
                names.push(arg.base_name);
            }
            // TODO: figure out nicer way to avoid name clashes
            let base_name = names.join("_$_");
            let specifics = deps.require_dep::<DomainEnc>(ty).unwrap();
            Ok((SnapshotEncOutput { base_name, snapshot, specifics }, ()))
        })
    }
}