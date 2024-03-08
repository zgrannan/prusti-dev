use std::fmt::Debug;

use prusti_rustc_interface::middle::mir;
use crate::{callable_idents::CallableIdent, debug_info::DebugInfo, refs::*, FunctionIdent, UnknownArity};
use std::collections::HashMap;


pub struct LocalData<'vir> {
    pub name: &'vir str, // TODO: identifiers
    pub ty: Type<'vir>,
    pub debug_info: DebugInfo,
}

#[derive(Eq, PartialEq)]
pub struct LocalDeclData<'vir> {
    pub name: &'vir str, // TODO: identifiers
    pub ty: Type<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum UnOpKind {
    Neg,
    Not,
}
impl From<mir::UnOp> for UnOpKind {
    fn from(value: mir::UnOp) -> Self {
        match value {
            mir::UnOp::Not => UnOpKind::Not,
            mir::UnOp::Neg => UnOpKind::Neg,
        }
    }
}
impl From<&mir::UnOp> for UnOpKind {
    fn from(value: &mir::UnOp) -> Self {
        UnOpKind::from(*value)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BinOpKind {
    CmpEq,
    CmpNe,
    CmpGt,
    CmpLt,
    CmpGe,
    CmpLe,
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // ...
}
impl From<mir::BinOp> for BinOpKind {
    fn from(value: mir::BinOp) -> Self {
        match value {
            mir::BinOp::Add => BinOpKind::Add,
            mir::BinOp::AddUnchecked => todo!(),
            mir::BinOp::Sub => BinOpKind::Sub,
            mir::BinOp::SubUnchecked => todo!(),
            mir::BinOp::Mul => BinOpKind::Mul,
            mir::BinOp::MulUnchecked => todo!(),
            mir::BinOp::Div => BinOpKind::Div,
            mir::BinOp::Rem => BinOpKind::Mod,
            mir::BinOp::BitXor => todo!(),
            // TODO: this is a temporary workaround,
            // we need to fix this for integers and
            // do non-short-circuiting for booleans.
            mir::BinOp::BitAnd => BinOpKind::And,
            mir::BinOp::BitOr => BinOpKind::Or,
            mir::BinOp::Shl => todo!(),
            mir::BinOp::ShlUnchecked => todo!(),
            mir::BinOp::Shr => todo!(),
            mir::BinOp::ShrUnchecked => todo!(),
            mir::BinOp::Eq => BinOpKind::CmpEq,
            mir::BinOp::Lt => BinOpKind::CmpLt,
            mir::BinOp::Le => BinOpKind::CmpLe,
            mir::BinOp::Ne => BinOpKind::CmpNe,
            mir::BinOp::Ge => BinOpKind::CmpGe,
            mir::BinOp::Gt => BinOpKind::CmpGt,
            mir::BinOp::Offset => todo!(),
        }
    }
}
impl From<&mir::BinOp> for BinOpKind {
    fn from(value: &mir::BinOp) -> Self {
        BinOpKind::from(*value)
    }
}

pub enum ConstData {
    Bool(bool),
    Int(u128), // TODO: what about negative numbers? larger numbers?
    Wildcard,
    Null,
}

impl ConstData {
    pub fn ty(&self) -> Type<'static> {
        match self {
            ConstData::Bool(_) => &TypeData::Bool,
            ConstData::Int(_) => &TypeData::Int,
            ConstData::Wildcard => &TypeData::Perm,
            ConstData::Null => &TypeData::Ref
        }
    }
}

#[derive(PartialEq, Eq, Ord, PartialOrd)]
pub enum TypeData<'vir> {
    Int,
    Bool,
    DomainTypeParam(DomainParamData<'vir>), // TODO: identifiers
    Domain(&'vir str, &'vir [Type<'vir>]), // TODO: identifiers
    // TODO: separate `TyParam` variant? `Domain` used for now
    Ref, // TODO: typed references ?
    Perm,
    Predicate, // The type of a predicate application
    Unsupported(UnsupportedType<'vir>)
}

#[derive(Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct UnsupportedType<'vir> {
    pub name: &'vir str,
}

pub type TySubsts<'vir> = HashMap<&'vir str, Type<'vir>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct DomainParamData<'vir> {
    pub name: &'vir str, // TODO: identifiers
}

pub struct FieldData<'vir> {
    pub(crate) name: &'vir str, // TODO: identifiers
    pub(crate) ty: Type<'vir>,
}

pub struct DomainFunctionData<'vir> {
    pub(crate) unique: bool,
    pub(crate) name: &'vir str, // TODO: identifiers
    pub(crate) args: &'vir [Type<'vir>],
    pub(crate) ret: Type<'vir>,
}

impl <'vir> DomainFunctionData<'vir> {
    pub fn ident(&self) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        FunctionIdent::new(self.name, UnknownArity::new(self.args), self.ret)
    }
}

pub enum CfgBlockLabelData {
    Start,
    End,
    BasicBlock(usize),
}

pub type AccFieldData<'vir> = crate::gendata::AccFieldGenData<'vir, !, !>;
pub type BinOpData<'vir> = crate::gendata::BinOpGenData<'vir, !, !>;
pub type CfgBlockData<'vir> = crate::gendata::CfgBlockGenData<'vir, !, !>;
pub type DomainAxiomData<'vir> = crate::gendata::DomainAxiomGenData<'vir, !, !>;
pub type DomainData<'vir> = crate::gendata::DomainGenData<'vir, !, !>;
pub type ExprData<'vir> = crate::gendata::ExprGenData<'vir, !, !>;
pub type ExprKindData<'vir> = crate::gendata::ExprKindGenData<'vir, ! ,!>;
pub type ForallData<'vir> = crate::gendata::ForallGenData<'vir, !, !>;
pub type FuncAppData<'vir> = crate::gendata::FuncAppGenData<'vir, !, !>;
pub type FunctionData<'vir> = crate::gendata::FunctionGenData<'vir, !, !>;
pub type GotoIfData<'vir> = crate::gendata::GotoIfGenData<'vir, !, !>;
pub type LetData<'vir> = crate::gendata::LetGenData<'vir, !, !>;
pub type MethodCallData<'vir> = crate::gendata::MethodCallGenData<'vir, !, !>;
pub type MethodData<'vir> = crate::gendata::MethodGenData<'vir, !, !>;
pub type PredicateAppData<'vir> = crate::gendata::PredicateAppGenData<'vir, !, !>;
pub type PredicateData<'vir> = crate::gendata::PredicateGenData<'vir, !, !>;
pub type ProgramData<'vir> = crate::gendata::ProgramGenData<'vir, !, !>;
pub type PureAssignData<'vir> = crate::gendata::PureAssignGenData<'vir, !, !>;
pub type StmtData<'vir> = crate::gendata::StmtGenData<'vir, !, !>;
pub type TerminatorStmtData<'vir> = crate::gendata::TerminatorStmtGenData<'vir, !, !>;
pub type TernaryData<'vir> = crate::gendata::TernaryGenData<'vir, !, !>;
pub type UnOpData<'vir> = crate::gendata::UnOpGenData<'vir, !, !>;
pub type UnfoldingData<'vir> = crate::gendata::UnfoldingGenData<'vir, !, !>;
