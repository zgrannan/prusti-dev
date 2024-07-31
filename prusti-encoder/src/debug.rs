use prusti_rustc_interface::{hir::def_id::DefId, middle::ty::GenericArgsRef};
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

pub fn fn_debug_name(def_id: DefId, substs: GenericArgsRef<'_>) -> String {
    vir::with_vcx(|vcx| vcx.tcx().def_path_str_with_args(def_id, substs))
}

pub fn visualization_data_dir(def_id: DefId, substs: GenericArgsRef<'_>) -> Option<String> {
    vir::with_vcx(|vcx| {
        let fn_debug_name = fn_debug_name(def_id, substs);
        let debug_dir = std::env::var("PCS_VIS_DATA_DIR").map(|dir| {
            let mut hasher = DefaultHasher::new();
            fn_debug_name.hash(&mut hasher);
            let hash = format!("{:x}", hasher.finish());
            format!("{}/{}", dir, hash)
        });
        debug_dir.ok()
    })
}
