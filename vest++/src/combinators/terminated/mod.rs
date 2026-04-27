//! Sequential composition discarding the suffix.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Parsing semantics: like `(A, B)`, but discards the value parsed by `B` and returns only the value parsed by `A`.
///
/// Serialization semantics: serializes `A` and then reuses `b_val` as the serialized witness for `B`.
///
/// When `CHECK` is `false`, parsing is malleable in the discarded suffix unless `B` admits a unique consistent value.
/// When `CHECK` is `true`, parsing additionally checks that the parsed suffix equals `b_val`.
pub struct Terminated2<A, B, BVal, const CHECK: bool = false> {
    pub a: A,
    pub b: B,
    pub b_val: BVal,
}

} // verus!
