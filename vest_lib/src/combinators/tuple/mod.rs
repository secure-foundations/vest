//! Sequential and dependent composition.
//!
//! [`Pair`] parses two formats in order; N-ary formats nest it as
//! `Pair(A, Pair(B, C))`. [`Bind`] chooses the second format based on the first's value.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Sequential composition of formats `A` and `B`.
#[derive(Copy)]
pub struct Pair<A, B>(pub A, pub B);

impl<A: Clone, B: Clone> Clone for Pair<A, B> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
    {
        Pair(self.0.clone(), self.1.clone())
    }
}

/// Sequential composition of formats `A` and `B`, where `B` may depend on the value of `A`.
///
/// Parsing semantics: parses `A` to get a `key`, then parses `B(key)` to get the body `value`,
/// and returns `(key, value)`.
/// During serialization, the caller must provide both the `key` and `value`.
///
/// ## Note on usage
///
/// Prefer [`super::Implicit`] when the key should be recovered from the body value instead of
/// being carried explicitly through the value type.
#[derive(Copy)]
pub struct Bind<A, B>(pub A, pub B);

impl<A: Clone, B: Clone> Clone for Bind<A, B> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
    {
        Bind(self.0.clone(), self.1.clone())
    }
}

} // verus!
