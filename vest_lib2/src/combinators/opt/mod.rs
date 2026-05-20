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
pub struct Opt<A>(pub A);

/// Optional field with an arbitrary continuation, defined as `Pair(Opt<A>, B)`.
///
/// ## Unambiguity
///
/// Requires `disjoint_domains(A, B)`.
pub struct Optional<A, B>(pub A, pub B);

} // verus!
