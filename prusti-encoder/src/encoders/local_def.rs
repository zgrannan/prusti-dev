use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{
    snapshot::SnapshotEncOutputRef, CapabilityEnc, PredicateEncOutputRef, SnapshotEnc,
};

pub struct MirLocalFieldEnc;

#[derive(Debug, Clone, Copy)]
pub struct MirLocalFieldEncOutput<'vir> {
    pub name: &'vir str,
    pub field: vir::Field<'vir>,
}

impl TaskEncoder for MirLocalFieldEnc {
    task_encoder::encoder_cache!(MirLocalFieldEnc);

    type TaskDescription<'tcx> = (
        DefId,                    // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
    );

    type OutputFullLocal<'vir> = MirLocalFieldEncOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

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
        deps.emit_output_ref::<Self>(*task_key, ());
        let (def_id, substs, cdid) = *task_key;
        let extra: String = substs.types().map(|s| format!("_{s}")).collect();
        let cdid = cdid
            .map(|cdid| format!("_{}_{}", cdid.krate, cdid.index.index()))
            .unwrap_or_default();
        vir::with_vcx(|vcx| {
            let name = vir::vir_format!(vcx, "{}{extra}{cdid}", vcx.tcx.item_name(def_id));
            let field = vcx.mk_field(vir::vir_format!(vcx, "local_{name}"), &vir::TypeData::Ref);
            Ok(((MirLocalFieldEncOutput { name, field }), ()))
        })
    }
}

pub struct MirLocalDefEnc;
#[derive(Clone, Copy)]
pub struct MirLocalDefEncOutput<'vir> {
    pub inputs: &'vir Vec<LocalDef<'vir>>,
    pub output: LocalDef<'vir>,
    pub field: MirLocalFieldEncOutput<'vir>,
    pub locals: Option<&'vir IndexVec<mir::Local, LocalDef<'vir>>>,
}
impl<'vir> MirLocalDefEncOutput<'vir> {
    pub fn local_to_arg(&self, local: mir::Local) -> (bool, &LocalDef<'vir>) {
        if local == mir::RETURN_PLACE {
            (true, &self.output)
        } else {
            (false, &self.inputs[local.index() - 1])
        }
    }
}

pub type MirLocalDefEncError = ();

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::Local<'vir>,
    pub pure_local_ex: vir::Expr<'vir>,
    pub ty: &'vir SnapshotEncOutputRef<'vir>,
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'tcx> = (
        DefId,                    // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
    );

    type OutputFullLocal<'vir> = MirLocalDefEncOutput<'vir>;

    type EncodingError = MirLocalDefEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

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
        let (def_id, substs, caller_def_id) = *task_key;
        deps.emit_output_ref::<Self>(*task_key, ());
        fn mk_local_def<'vir, 'tcx>(
            vcx: &'vir vir::VirCtxt<'tcx>,
            name: &'vir str,
            ty: SnapshotEncOutputRef<'vir>,
        ) -> LocalDef<'vir> {
            let local = vcx.mk_local(name, ty.snapshot);
            let pure_local_ex = vcx.mk_local_ex_local(local);
            LocalDef {
                local,
                pure_local_ex,
                ty: vcx.alloc(ty),
            }
        }

        vir::with_vcx(|vcx| {
            let param_env = vcx.tcx.param_env(caller_def_id.unwrap_or(def_id));
            let sig = vcx.tcx.subst_and_normalize_erasing_regions(
                substs,
                param_env,
                vcx.tcx.fn_sig(def_id),
            );
            let sig = sig.skip_binder();

            let inputs: Vec<_> = (0..sig.inputs().len())
                .map(|i| {
                    mk_local_def(
                        vcx,
                        vir::vir_format!(vcx, "arg{i}"),
                        deps.require_ref::<SnapshotEnc>(sig.inputs()[i]).unwrap(),
                    )
                })
                .collect();
            let output = mk_local_def(
                vcx,
                "res",
                deps.require_ref::<SnapshotEnc>(sig.output()).unwrap(),
            );
            let field = deps.require_local::<MirLocalFieldEnc>(*task_key).unwrap();

            let locals = vcx.body.borrow_mut().get_any_fn_body(def_id).map(|body| {
                vcx.alloc(IndexVec::from_fn_n(
                    |arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}p", arg.index());
                        let ty = deps
                            .require_ref::<SnapshotEnc>(body.local_decls()[arg].ty)
                            .unwrap();
                        mk_local_def(vcx, local, ty)
                    },
                    body.local_decls().len(),
                ))
            });
            Ok((
                MirLocalDefEncOutput {
                    inputs: vcx.alloc(inputs),
                    output,
                    field,
                    locals,
                },
                (),
            ))
        })
    }
}
