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
#[derive(Copy)]
pub struct Preceded<A, AVal, B, const CHECK: bool = false> {
    pub a: A,
    pub b: B,
    pub a_val: AVal,
}

impl<A: Clone, AVal: Clone, B: Clone, const CHECK: bool> Clone for Preceded<A, AVal, B, CHECK> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.a,), cloned.a),
            call_ensures(B::clone, (&self.b,), cloned.b),
            call_ensures(AVal::clone, (&self.a_val,), cloned.a_val),
    {
        Preceded { a: self.a.clone(), b: self.b.clone(), a_val: self.a_val.clone() }
    }
}

} // verus!
