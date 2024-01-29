use prusti_rustc_interface::{
    middle::{ty::{self, TyKind}},
};
use task_encoder::{TaskEncoder, TaskEncoderDependencies, TaskEncoderError};

use crate::util::{extract_type_params, MostGenericTy};

pub mod predicate;
pub mod generic_predicate;
pub mod domain;
pub mod generic_snapshot;
pub mod snapshot;
pub mod viper_tuple;
