use prusti_rustc_interface::hir::def_id::DefId;
use std::collections::{BTreeMap, BTreeSet};

use crate::ViperIdent;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Identifiable<'tcx> {
    SymFunction(FunctionCallTaskDescription<'tcx>),
}

pub struct Interner<'tcx, 'vir> {
    map: BTreeMap<Identifiable<'tcx>, ViperIdent<'vir>>,
    used_identifiers: BTreeSet<ViperIdent<'vir>>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
            used_identifiers: BTreeSet::new(),
        }
    }

    // pub fn get_ident<'vir>(
    //     &'vir mut self,
    //     identifiable: Identifiable,
    //     preferred_ident: impl Fn() -> ViperIdent<'vir>,
    //     long_ident: impl Fn() -> ViperIdent<'vir>,
    // ) -> ViperIdent<'vir> {
    //     let ident = self.map.get(&identifiable);
    //     if let Some(ident) = ident {
    //         return *ident;
    //     } else {
    //         let ident = preferred_ident();
    //         let ident = if self.used_identifiers.contains(&ident) {
    //             long_ident()
    //         } else {
    //             ident
    //         };
    //         assert!(!self.used_identifiers.contains(&ident));
    //         let ident: ViperIdent<'static> =
    //             ViperIdent::new(Box::leak(Box::new(ident.to_str().to_string())));
    //         self.used_identifiers.insert(ident);
    //         self.map.insert(identifiable, ident);
    //         ident
    //     }
    // }
}
