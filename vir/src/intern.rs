use std::collections::{BTreeMap, BTreeSet};

use crate::ViperIdent;

pub type FullIdent = String;
pub type ShortIdent = String;

pub trait Identifiable {
    fn to_full_ident(&self) -> FullIdent;
    fn preferred_idents(&self) -> impl Iterator<Item = String>;
}

pub struct Interner {
    map: BTreeMap<FullIdent, &'static str>,
    used_identifiers: BTreeSet<&'static str>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
            used_identifiers: BTreeSet::new(),
        }
    }

    pub fn get_ident<T: Identifiable>(&mut self, identifiable: T) -> ViperIdent<'static> {
        let full_ident = identifiable.to_full_ident();
        let ident = self.map.get(&full_ident);
        if let Some(ident) = ident {
            return ViperIdent::new(ident);
        } else {
            for ident in identifiable
                .preferred_idents()
                .chain(std::iter::once(full_ident.clone()))
            {
                if !self.used_identifiers.contains(&ident.as_str()) {
                    let ident = ViperIdent::sanitize_str(&ident);
                    let ident = Box::leak(Box::new(ident));
                    self.used_identifiers.insert(ident);
                    self.map.insert(full_ident, ident);
                    return ViperIdent::new(ident);
                }
            }
            unreachable!()
        }
    }
}
