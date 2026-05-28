//! Optional field combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Optional combinator: denotes an optional field.
///
/// Parsing semantics: tries `A`, returning `Some(a)` on success; on failure, returns `None` without consuming input.
///
/// Serialization semantics: if the value is `Some(a)`, serializes `a` with `A`; if the value is `None`, produces no output.
///
/// ## Consistency
///
/// A value `v` is consistent with `Opt<A>` iff either `v` is consistent with `A` or `v` is `None`.
///
/// ## Note
///
/// This combinator is mostly used *internally* to specify [`Optional<A, B>`], which is
/// able to disambiguate `A` and `B` and hence more compositional.
#[derive(Copy)]
pub struct Opt<A>(pub A);

impl<A: Clone> Clone for Opt<A> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
    {
        Opt(self.0.clone())
    }
}

/// Optional field with an arbitrary continuation, defined as `Pair(Opt<A>, B)`.
///
/// ## Unambiguity
///
/// Requires `disjoint_domains(A, B)`.
#[derive(Copy)]
pub struct Optional<A, B>(pub A, pub B);

impl<A: Clone, B: Clone> Clone for Optional<A, B> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
    {
        Optional(self.0.clone(), self.1.clone())
    }
}

} // verus!
