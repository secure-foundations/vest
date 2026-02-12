pub mod proof;
pub mod spec;

use crate::core::spec::Consistency;
use vstd::prelude::*;

verus! {

/// The sequentially dependent combinator.
///
/// - parse: parse `A` first, then parse `B(a)` where `a` is the parsed result of `A`. Only return the parsed value of `B(a)`
/// - serialize: infer the implicit `a` from the output value and serialize `B(a)`, then serialize `A` with the inferred `a`.
pub struct Implicit<A, B>(pub A, pub B);

/// Dependent sequential combinator with user-provided recovery logic.
///
/// Like [`Implicit`], but uses an explicit `recover` function to get back the
/// original `a` from the output value for consistency checking and serialization.
pub struct ImplicitAuto<A, B, Recover>(pub A, pub B, pub Recover);

/// Lossless key embedding condition for [`Implicit`]
pub trait LosslessImplicit<A: Consistency, B: Consistency> {
    proof fn lemma_value_uniquely_determines_key(
        fmt: &Implicit<A, spec_fn(A::Val) -> B>,
        k1: A::Val,
        k2: A::Val,
        value: B::Val,
    )
        ensures
            fmt.0.consistent(k1) && (fmt.1)(k1).consistent(value) && fmt.0.consistent(k2) && (
            fmt.1)(k2).consistent(value) ==> k1 == k2,
    ;
}

/// Lossless key embedding condition for [`ImplicitAuto`]
pub trait LosslessImplicitAuto<A: Consistency, B: Consistency> {
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
