#![feature(rustc_private)]
#![feature(never_type)]
#![feature(iter_intersperse)]
#![feature(return_position_impl_trait_in_trait)]

mod context;
mod data;
mod debug;
mod debug_info;
mod gendata;
mod genrefs; // TODO: explain gen...
mod macros;
mod make;
mod refs;
mod reify;
mod serde;
mod callable_idents;
mod viper_ident;
mod intern;

pub use context::*;
pub use data::*;
pub use gendata::*;
pub use genrefs::*;
pub use refs::*;
pub use reify::*;
pub use callable_idents::*;
pub use viper_ident::*;
pub use intern::*;

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
