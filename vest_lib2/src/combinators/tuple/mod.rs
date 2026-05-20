//! Sequential composition for pairs.
//! N-ary formats are built by nesting: `Pair(A, Pair(B, C))`.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Sequential composition of formats `A` and `B`.
pub struct Pair<A, B>(pub A, pub B);

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
pub struct Bind<A, B>(pub A, pub B);

} // verus!
