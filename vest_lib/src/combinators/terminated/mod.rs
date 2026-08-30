//! Sequential composition that discards a suffix value.
//!
//! [`Terminated`] exposes the first value and uses the second format as framing,
//! such as an end marker that can be reconstructed during serialization.
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
#[derive(Copy)]
pub struct Terminated<A, B, BVal, const CHECK: bool = false> {
    pub a: A,
    pub b: B,
    pub b_val: BVal,
}

impl<A: Clone, B: Clone, BVal: Clone, const CHECK: bool> Clone for Terminated<A, B, BVal, CHECK> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.a,), cloned.a),
            call_ensures(B::clone, (&self.b,), cloned.b),
            call_ensures(BVal::clone, (&self.b_val,), cloned.b_val),
    {
        Terminated { a: self.a.clone(), b: self.b.clone(), b_val: self.b_val.clone() }
    }
}

} // verus!
