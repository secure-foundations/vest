//! Fixed- and variable-length byte sequence combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use vstd::prelude::*;

use super::AsLen;

verus! {

/// Parses/serializes exactly `N` bytes as `Seq<u8>`.
#[derive(Clone, Copy)]
pub struct Fixed<const N: usize>;

/// Parses/serializes a variable-length byte sequence `Seq<u8>`.
///
/// The length is determined by `self.0`, which must implement [`super::length::AsLen`] and
/// defaults to `u8`.
///
/// ## Consistency
///
/// A byte sequence is consistent w.r.t `Varied` iff its length equals `self.0`.
#[derive(Copy)]
pub struct Varied<Len = u8>(pub Len);

impl<Len: Clone> Clone for Varied<Len> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Len::clone, (&self.0,), cloned.0),
    {
        Varied(self.0.clone())
    }
}

/// Wraps an inner combinator, constraining it to consume/produce exactly `self.0` bytes.
///
/// Implemented as `AndThen(Varied(self.0), self.1)`.
///
/// ## Consistency
///
/// A value of type `Inner::Val` is consistent w.r.t `ExactLen` iff it is consistent w.r.t `Inner` and
/// its byte length given by `Inner` equals `self.0`.
#[derive(Copy)]
pub struct ExactLen<Inner, Len = u8>(pub Len, pub Inner);

impl<Inner: Clone, Len: Clone> Clone for ExactLen<Inner, Len> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Len::clone, (&self.0,), cloned.0),
            call_ensures(Inner::clone, (&self.1,), cloned.1),
    {
        ExactLen(self.0.clone(), self.1.clone())
    }
}

/// Run a [bytes combinator](crate::core::spec::BytesCombinator) `A` and then
/// re-interpret the *entire* bytes consumed/produced by `A` with another combinator `B`.
///
/// ## Consistency
///
/// A value of type `B::Val` is consistent w.r.t `AndThen<A, B>` iff there exists a value of type
/// `A::Val` that is consistent w.r.t `A` and whose byte length equals the byte length of the `B::Val` value w.r.t `B`.
/// Prefer [`ExactLen`] over `AndThen` to avoid the existential reasoning in the consistency condition.
#[derive(Copy)]
pub struct AndThen<A, B>(pub A, pub B);

impl<A: Clone, B: Clone> Clone for AndThen<A, B> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
    {
        AndThen(self.0.clone(), self.1.clone())
    }
}

impl<const N: usize> LeafNonMalleable for Fixed<N> {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl<Len: AsLen> LeafNonMalleable for Varied<Len> {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
