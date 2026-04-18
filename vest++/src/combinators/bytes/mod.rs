//! Fixed- and variable-length byte sequence combinators.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use vstd::prelude::*;

use super::AsLen;

verus! {

/// Parses/serializes exactly `N` bytes as `Seq<u8>`.
pub struct Fixed<const N: usize>;

/// Parses/serializes a variable-length byte sequence `Seq<u8>`.
///
/// The length is determined by `self.0`, which must implement [`super::length::AsLen`] and
/// defaults to `u8`.
///
/// ## Consistency
///
/// A byte sequence is consistent w.r.t `Varied` iff its length equals `self.0`.
pub struct Varied<Len = u8>(pub Len);

/// Wraps an inner combinator, constraining it to consume/produce exactly `self.0` bytes.
///
/// Implemented as `AndThen(Varied(self.0), self.1)`.
///
/// ## Consistency
///
/// A value of type `Inner::Val` is consistent w.r.t `ExactLen` iff it is consistent w.r.t `Inner` and
/// its byte length given by `Inner` equals `self.0`.
pub struct ExactLen<Inner, Len = u8>(pub Len, pub Inner);

/// Run a [bytes combinator](crate::core::spec::BytesCombinator) `A` and then
/// re-interpret the *entire* bytes consumed/produced by `A` with another combinator `B`.
///
/// ## Consistency
///
/// A value of type `B::Val` is consistent w.r.t `AndThen<A, B>` iff there exists a value of type
/// `A::Val` that is consistent w.r.t `A` and whose byte length equals the byte length of the `B::Val` value w.r.t `B`.
/// Prefer [`ExactLen`] over `AndThen` to avoid the existential reasoning in the consistency condition.
pub struct AndThen<A, B>(pub A, pub B);

impl<const N: usize> LeafNonMalleable for Fixed<N> {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl<Len: AsLen> LeafNonMalleable for Varied<Len> {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
