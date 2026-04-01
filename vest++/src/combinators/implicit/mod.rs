//! Implicit sequential dependency combinators.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::Consistency;
use vstd::prelude::*;

verus! {

/// (Sequential) dependent pair combinator.
///
/// Parsing semantics: parses `A` to get a `key`, then parses `B(key)` to get the body `value`,
/// and returns `(key, value)`.
/// During serialization, the caller must provide both the `key` and `value`, and the combinator verifies that
/// the `key` is consistent with `A` and the `value` is consistent with `B(key)`.
///
/// ## Note on usage
///
/// Prefer [`super::Bind`] to avoid manually recovering the key during serialization.
pub struct DepPair<A, B>(pub A, pub B);

/// Dependent sequential combinator with explicit recovery function.
pub struct ImplicitAuto<A, B, Recover>(pub A, pub B, pub Recover);

/// Lossless key embedding condition for [`Implicit`].
///
/// Ensures the body value uniquely determines the key.
pub trait LosslessImplicit<A: Consistency, B: Consistency> {
    /// The body value uniquely determines the key.
    proof fn lemma_value_uniquely_determines_key(
        fmt: &DepPair<A, spec_fn(A::Val) -> B>,
        k1: A::Val,
        k2: A::Val,
        value: B::Val,
    )
        ensures
            fmt.0.consistent(k1) && (fmt.1)(k1).consistent(value) && fmt.0.consistent(k2) && (
            fmt.1)(k2).consistent(value) ==> k1 == k2,
    ;
}

/// Lossless key embedding condition for [`ImplicitAuto`].
///
/// Same uniqueness property as [`LosslessImplicit`].
pub trait LosslessImplicitAuto<A: Consistency, B: Consistency> {
    /// The body value uniquely determines the key.
    proof fn lemma_value_determines_key(
        fmt: &ImplicitAuto<A, spec_fn(A::Val) -> B, spec_fn(B::Val) -> A::Val>,
        k1: A::Val,
        k2: A::Val,
        value: B::Val,
    )
        ensures
            fmt.0.consistent(k1) && (fmt.1)(k1).consistent(value) && fmt.0.consistent(k2) && (
            fmt.1)(k2).consistent(value) ==> k1 == k2,
    ;
}

} // verus!
