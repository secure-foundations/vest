//! Predicate refinement and constant-value formats.
//!
//! [`Refined`] keeps only values satisfying a predicate. [`Const`] fixes that value and is commonly used for static tags or discriminants.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Value refinement combinator: filters values through a predicate.
///
/// ## Consistency
///
/// `inner.consistent(v) && predicate.apply(v)`.
#[derive(Copy)]
pub struct Refined<Inner, Predicate>(pub Inner, pub Predicate);

impl<Inner: Clone, Predicate: Clone> Clone for Refined<Inner, Predicate> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.0,), cloned.0),
            call_ensures(Predicate::clone, (&self.1,), cloned.1),
    {
        Refined(self.0.clone(), self.1.clone())
    }
}

/// Constant-value combinator: matches a specific constant value.
///
/// Parsing semantics: parses with `inner` and succeeds only if the result equals the expected value.
/// The matched constant value itself is returned.
///
/// Implements [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal).
#[derive(Copy)]
pub struct Const<Inner, Value>(pub Inner, pub Value);

impl<Inner: Clone, Value: Clone> Clone for Const<Inner, Value> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.0,), cloned.0),
            call_ensures(Value::clone, (&self.1,), cloned.1),
    {
        Const(self.0.clone(), self.1.clone())
    }
}

/// Sugar for `Preceded { a: Const(inner, tag), a_val: tag, b: body }`.
#[derive(Copy)]
pub struct PrefixTagged<Tg, Tag, Of>(pub Tg, pub Tag, pub Of);

impl<Tg: Clone, Tag: Clone, Of: Clone> Clone for PrefixTagged<Tg, Tag, Of> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Tg::clone, (&self.0,), cloned.0),
            call_ensures(Tag::clone, (&self.1,), cloned.1),
            call_ensures(Of::clone, (&self.2,), cloned.2),
    {
        PrefixTagged(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

/// Sugar for `Terminated { a: body, b: Const(inner, tag), b_val: tag }`.
#[derive(Copy)]
pub struct SuffixTagged<Of, Tg, Tag>(pub Of, pub Tg, pub Tag);

impl<Of: Clone, Tg: Clone, Tag: Clone> Clone for SuffixTagged<Of, Tg, Tag> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Of::clone, (&self.0,), cloned.0),
            call_ensures(Tg::clone, (&self.1,), cloned.1),
            call_ensures(Tag::clone, (&self.2,), cloned.2),
    {
        SuffixTagged(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

} // verus!
