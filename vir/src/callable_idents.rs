use crate::{
    debug_info::DebugInfo, DomainParamData, ExprGen, MethodCallGenData, PredicateAppGen,
    PredicateAppGenData, StmtGenData, TySubsts, Type, TypeData, VirCtxt, LocalDecl,
};
use sealed::sealed;
use std::collections::HashMap;

pub trait CallableIdent<'vir, A: Arity<'vir>, ResultTy> {
    fn new(name: &'vir str, args: A, result_ty: ResultTy) -> Self;
    fn name(&self) -> &'vir str;
    fn arity(&self) -> &A;
    fn result_ty(&self) -> ResultTy;
}
pub trait ToKnownArity<'vir, T: 'vir, ResultTy>:
    CallableIdent<'vir, UnknownArityAny<'vir, T>, ResultTy> + Sized
{
    fn to_known<
        'tcx,
        K: CallableIdent<'vir, KnownArityAny<'vir, T, N>, ResultTy>,
        const N: usize,
    >(
        self,
    ) -> K {
        K::new(
            self.name(),
            KnownArityAny::new(self.arity().args().try_into().unwrap()),
            self.result_ty(),
        )
    }
}
impl<'vir, T: 'vir, ResultTy, K: CallableIdent<'vir, UnknownArityAny<'vir, T>, ResultTy>>
    ToKnownArity<'vir, T, ResultTy> for K
{
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct FunctionIdent<'vir, A: Arity<'vir>>(&'vir str, A, Type<'vir>, DebugInfo);

impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, Type<'vir>> for FunctionIdent<'vir, A> {
    fn new(name: &'vir str, args: A, result_ty: Type<'vir>) -> Self {
        Self(name, args, result_ty, DebugInfo::new())
    }

    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }

    fn result_ty(&self) -> Type<'vir> {
        self.2
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> FunctionIdent<'vir, A> {
    pub fn debug_info(&self) -> DebugInfo {
        self.3
    }

    pub fn as_unknown_arity(self) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        FunctionIdent(
            self.name(),
            UnknownArity::new(self.1.args()),
            self.result_ty(),
            self.debug_info(),
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MethodIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for MethodIdent<'vir, A> {
    fn new(name: &'vir str, args: A, _unused: ()) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}

impl<'vir, A: Arity<'vir>> MethodIdent<'vir, A> {
    pub fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
}

impl<'vir, A: Arity<'vir, Arg=Type<'vir>>> MethodIdent<'vir, A> {
    pub fn as_unknown_arity(self) -> MethodIdent<'vir, UnknownArity<'vir>> {
        MethodIdent(
            self.name(),
            UnknownArity::new(self.1.args())
        )
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct PredicateIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for PredicateIdent<'vir, A> {
    fn new(name: &'vir str, args: A, _unused: ()) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> PredicateIdent<'vir, A> {
    pub fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    pub fn as_unknown_arity(self) -> PredicateIdent<'vir, UnknownArity<'vir>> {
        PredicateIdent(self.0, UnknownArity::new(self.1.args()))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DomainIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for DomainIdent<'vir, A> {
    fn new(name: &'vir str, args: A, _unused: ()) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}

impl<'vir> DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>> {
    pub fn nullary(name: &'vir str) -> Self {
        Self(name, KnownArityAny::new(&[]))
    }
}

pub type DomainIdentUnknownArity<'vir> =
    DomainIdent<'vir, UnknownArityAny<'vir, DomainParamData<'vir>>>;

impl<'vir> DomainIdentUnknownArity<'vir> {
    pub fn new(name: &'vir str, args: UnknownArityAny<'vir, DomainParamData<'vir>>) -> Self {
        Self(name, args)
    }
}

#[sealed]
pub trait Arity<'vir>: Copy {
    type Arg;
    fn args(&self) -> &'vir [Self::Arg];

    #[must_use]
    fn len_matches(&self, len: usize) -> bool;
}
#[sealed]
impl<'vir, T, const N: usize> Arity<'vir> for KnownArityAny<'vir, T, N> {
    type Arg = T;
    fn args(&self) -> &'vir [T] {
        &self.0
    }
    fn len_matches(&self, _len: usize) -> bool {
        true
    }
}
#[sealed]
impl<'vir, T> Arity<'vir> for UnknownArityAny<'vir, T> {
    type Arg = T;
    fn args(&self) -> &'vir [T] {
        &self.0
    }

    fn len_matches(&self, len: usize) -> bool {
        self.0.len() == len
    }
}

pub trait HasType<'vir> {
    fn typ(&self) -> Type<'vir>;
}

impl <'vir, Curr, Next> HasType<'vir> for ExprGen<'vir, Curr, Next> {
    fn typ(&self) -> Type<'vir> {
        self.ty()
    }
}

impl <'vir> HasType<'vir> for LocalDecl<'vir> {
    fn typ(&self) -> Type<'vir> {
        self.ty
    }
}

pub trait CheckTypes<'vir> {
    #[must_use]
    fn types_match<T: HasType<'vir>>(
        &self,
        args: &[T],
    ) -> bool;
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> CheckTypes<'vir> for A {
    fn types_match<T: HasType<'vir>>(
        &self,
        args: &[T],
    ) -> bool {
        if !self.len_matches(args.len()) {
            return false;
        }
        args.iter().zip(self.args().into_iter()).all(|(a, expected)| {
            a.typ() == *expected
        })
    }
}

#[derive(Debug)]
pub struct KnownArityAny<'vir, T, const N: usize>(&'vir [T]);
impl<'vir, T, const N: usize> KnownArityAny<'vir, T, N> {
    pub const fn new(types: &'vir [T; N]) -> Self {
        Self(types)
    }
}
impl<'vir, T, const N: usize> Clone for KnownArityAny<'vir, T, N> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<'vir, T, const N: usize> Copy for KnownArityAny<'vir, T, N> {}
pub type KnownArity<'vir, const N: usize> = KnownArityAny<'vir, Type<'vir>, N>;
pub type NullaryArity<'vir> = KnownArity<'vir, 0>;
pub type UnaryArity<'vir> = KnownArity<'vir, 1>;
pub type BinaryArity<'vir> = KnownArity<'vir, 2>;
pub type TernaryArity<'vir> = KnownArity<'vir, 3>;

#[derive(Debug)]
pub struct UnknownArityAny<'vir, T>(&'vir [T]);
impl<'vir, T> UnknownArityAny<'vir, T> {
    pub const fn new(types: &'vir [T]) -> Self {
        Self(types)
    }
}
impl<'vir, T> Clone for UnknownArityAny<'vir, T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<'vir, T> Copy for UnknownArityAny<'vir, T> {}
pub type UnknownArity<'vir> = UnknownArityAny<'vir, Type<'vir>>;

// Func arity known at compile time
// TODO: maybe take `args: &[T; N]` instead?

impl<'vir, const N: usize> FunctionIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N],
    ) -> ExprGen<'vir, Curr, Next> {
        if self.1.types_match(&args) {
            vcx.mk_func_app(self.name(), &args, self.result_ty())
        } else {
            panic!(
                "Function {} could not be applied, debug info: {}",
                self.name(),
                self.debug_info()
            );
        }
    }
}

impl<'vir, const N: usize> PredicateIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next> {
        assert!(self.1.types_match(&args));
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(&args),
            perm,
        })
    }
}
impl<'vir, const N: usize> MethodIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N],
    ) -> StmtGenData<'vir, Curr, Next> {
        assert!(self.1.types_match(&args));
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(&args),
        }))
    }
}
impl<'vir, const N: usize> DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, N>> {
    pub fn apply<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, args: [Type<'vir>; N]) -> Type<'vir> {
        vcx.alloc(TypeData::Domain(self.0, vcx.alloc_slice(&args)))
    }
}

pub trait Caster<'vir> {
    fn is_generic(&self, ty: Type<'vir>) -> bool;
    fn upcast<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'_>,
        expr: ExprGen<'vir, Curr, Next>) -> ExprGen<'vir, Curr, Next>;
    fn downcast<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'_>,
        expr: ExprGen<'vir, Curr, Next>
    ) -> ExprGen<'vir, Curr, Next>;
}

// Func arity checked at runtime

impl<'vir> FunctionIdent<'vir, UnknownArity<'vir>> {
    pub fn apply_with_casts<'tcx, Curr: 'vir, Next: 'vir, C: Caster<'vir>>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
        caster: C,
    ) -> ExprGen<'vir, Curr, Next> {
        let args = args
            .iter()
            .zip(self.arity().args().iter())
            .map(|(a, expected)| {
                let arg_generic = caster.is_generic(a.typ());
                let expected_generic = caster.is_generic(expected);
                if arg_generic && !expected_generic {
                    eprintln!("upcasting");
                    caster.downcast(vcx, a)
                } else if !arg_generic && expected_generic {
                    eprintln!("downcasting");
                    caster.upcast(vcx, a)
                } else {
                    eprintln!("no cast");
                    a
                }
            })
            .collect::<Vec<_>>();
        let args = vcx.alloc_slice(&args);
        if self.1.types_match(args) {
            vcx.mk_func_app(self.name(), args, self.result_ty())
        } else {
            panic!(
                "Function {} could not be applied, debug info: {}",
                self.name(),
                self.debug_info()
            )
        }
    }
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
    ) -> ExprGen<'vir, Curr, Next> {
        if self.1.types_match(args) {
            vcx.mk_func_app(self.name(), args, self.result_ty())
        } else {
            panic!(
                "Function {} could not be applied, debug info: {}",
                self.name(),
                self.debug_info()
            );
        }
    }
}

impl<'vir> PredicateIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next> {
        assert!(self.1.types_match(args));
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(args),
            perm,
        })
    }
}
impl<'vir> MethodIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
    ) -> StmtGenData<'vir, Curr, Next> {
        assert!(self.1.types_match(args));
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(args),
        }))
    }
}
impl<'vir> DomainIdent<'vir, UnknownArityAny<'vir, DomainParamData<'vir>>> {
    pub fn apply<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, args: &[Type<'vir>]) -> Type<'vir> {
        assert!(self.1.len_matches(args.len()));
        vcx.alloc(TypeData::Domain(self.0, vcx.alloc_slice(args)))
    }
}
