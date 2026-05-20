//! Sequential composition discarding the prefix.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Parsing semantics: like `(A, B)`, but discards the value parsed by `A` and returns only the value parsed by `B`.
///
/// Serialization semantics: reuses `a_val` as the serialized witness for `A`, then serializes `B`.
///
/// When `CHECK` is `false`, parsing is malleable in the discarded prefix unless `A` admits a unique consistent value.
/// When `CHECK` is `true`, parsing additionally checks that the parsed prefix equals `a_val`.
pub struct Preceded<A, AVal, B, const CHECK: bool = false> {
    pub a: A,
    pub b: B,
    pub a_val: AVal,
}

} // verus!
