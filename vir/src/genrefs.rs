pub type AccFieldGen<'vir, Curr, Next> = &'vir crate::gendata::AccFieldGenData<'vir, Curr, Next>;
pub type BinOpGen<'vir, Curr, Next> = &'vir crate::gendata::BinOpGenData<'vir, Curr, Next>;
pub type CfgBlockGen<'vir, Curr, Next> = &'vir crate::gendata::CfgBlockGenData<'vir, Curr, Next>;
pub type DomainAxiomGen<'vir, Curr, Next> = &'vir crate::gendata::DomainAxiomGenData<'vir, Curr, Next>;
pub type DomainGen<'vir, Curr, Next> = &'vir crate::gendata::DomainGenData<'vir, Curr, Next>;
pub type ExprGen<'vir, Curr, Next> = &'vir crate::gendata::ExprGenData<'vir, Curr, Next>;
pub type ExprKindGen<'vir, Curr, Next> = &'vir crate::gendata::ExprKindGenData<'vir, Curr, Next>;
pub type ForallGen<'vir, Curr, Next> = &'vir crate::gendata::ForallGenData<'vir, Curr, Next>;
pub type FuncAppGen<'vir, Curr, Next> = &'vir crate::gendata::FuncAppGenData<'vir, Curr, Next>;
pub type FunctionGen<'vir, Curr, Next> = &'vir crate::gendata::FunctionGenData<'vir, Curr, Next>;
pub type GotoIfGen<'vir, Curr, Next> = &'vir crate::gendata::GotoIfGenData<'vir, Curr, Next>;
pub type LetGen<'vir, Curr, Next> = &'vir crate::gendata::LetGenData<'vir, Curr, Next>;
pub type MacroGen<'vir, Curr, Next> = &'vir crate::gendata::MacroGenData<'vir, Curr, Next>;
pub type MethodGen<'vir, Curr, Next> = &'vir crate::gendata::MethodGenData<'vir, Curr, Next>;
pub type MethodCallGen<'vir, Curr, Next> = &'vir crate::gendata::MethodCallGenData<'vir, Curr, Next>;
pub type PredicateGen<'vir, Curr, Next> = &'vir crate::gendata::PredicateGenData<'vir, Curr, Next>;
pub type PredicateAppGen<'vir, Curr, Next> = &'vir crate::gendata::PredicateAppGenData<'vir, Curr, Next>;
pub type ProgramGen<'vir, Curr, Next> = &'vir crate::gendata::ProgramGenData<'vir, Curr, Next>;
pub type PureAssignGen<'vir, Curr, Next> = &'vir crate::gendata::PureAssignGenData<'vir, Curr, Next>;
pub type StmtGen<'vir, Curr, Next> = &'vir crate::gendata::StmtGenData<'vir, Curr, Next>;
pub type TerminatorStmtGen<'vir, Curr, Next> = &'vir crate::gendata::TerminatorStmtGenData<'vir, Curr, Next>;
pub type TernaryGen<'vir, Curr, Next> = &'vir crate::gendata::TernaryGenData<'vir, Curr, Next>;
pub type UnOpGen<'vir, Curr, Next> = &'vir crate::gendata::UnOpGenData<'vir, Curr, Next>;
pub type UnfoldingGen<'vir, Curr, Next> = &'vir crate::gendata::UnfoldingGenData<'vir, Curr, Next>;
