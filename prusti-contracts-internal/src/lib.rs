extern crate proc_macro;

use proc_macro::TokenStream;
use prusti_specs::{rewrite_prusti_attributes, SpecAttributeKind};
use quote::quote;
use syn::{self, DeriveInput};

#[proc_macro_derive(PrustiClone)]
pub fn derive_clone(item: TokenStream) -> TokenStream {
    let input : DeriveInput = syn::parse(item).unwrap();
    let name = input.ident;
    (quote! {
      impl Clone for #name {
        #[trusted]
        fn clone(&self) -> Self {
            todo!()
        }
      }
    }).into()
}

#[proc_macro_derive(PrustiDeserialize)]
pub fn derive_deserialize(item: TokenStream) -> TokenStream {
    let input : DeriveInput = syn::parse(item).unwrap();
    let name = input.ident;
    (quote! {
      impl <'de> Deserialize<'de> for #name {
        #[trusted]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de> {
            todo!()
        }
      }
    }).into()
}

#[proc_macro_derive(PrustiDebug)]
pub fn derive_debug(item: TokenStream) -> TokenStream {
    let input : DeriveInput = syn::parse(item).unwrap();
    let name = input.ident;
    (quote! {
      impl std::fmt::Debug for #name {
        #[trusted]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            todo!()
        }
      }
    }).into()
}

#[proc_macro_derive(PrustiSerialize)]
pub fn derive_serialize(item: TokenStream) -> TokenStream {
    let input : DeriveInput = syn::parse(item).unwrap();
    let name = input.ident;
    (quote! {
      impl  Serialize for #name {
        #[trusted]
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer {
            todo!()
        }
      }
    }).into()
}

#[proc_macro_derive(PrustiEq)]
pub fn derive_eq(item: TokenStream) -> TokenStream {
    let input : DeriveInput = syn::parse(item).unwrap();
    let name = input.ident;
    (quote! {
      impl Eq for #name {
        fn assert_receiver_is_total_eq(&self){}
      }
    }).into()
}

#[proc_macro_derive(PrustiPartialEq)]
pub fn derive_partial_eq(item: TokenStream) -> TokenStream {
    let input : DeriveInput = syn::parse(item).unwrap();
    let name = input.ident;
    (quote! {
      impl PartialEq for #name {
        #[trusted]
        fn eq(&self, other: &#name) -> bool { todo!() }
      }
    }).into()
}

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Requires, attr.into(), tokens.into()).into()
}


#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Ensures, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn after_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::AfterExpiry, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn after_expiry_if(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::AfterExpiryIf, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn pure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Pure, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Trusted, attr.into(), tokens.into()).into()
}

#[proc_macro]
pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    prusti_specs::body_invariant(tokens.into()).into()
}

#[proc_macro]
pub fn closure(tokens: TokenStream) -> TokenStream {
    prusti_specs::closure(tokens.into(), false).into()
}

#[proc_macro_attribute]
pub fn refine_trait_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::refine_trait_spec(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::extern_spec(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::invariant(attr.into(), tokens.into()).into()
}

#[proc_macro]
pub fn predicate(tokens: TokenStream) -> TokenStream {
    prusti_specs::predicate(tokens.into()).into()
}
