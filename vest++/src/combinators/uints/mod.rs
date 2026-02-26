//! Unsigned integer combinators.

/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Unsigned 8-bit integer combinator. Reads/writes a single byte.
pub struct U8;

/// Little-endian unsigned 16-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<2>, mapper: U16LeMapper }`.
pub struct U16Le;

/// Big-endian unsigned 16-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<2>, mapper: U16BeMapper }`.
pub struct U16Be;

/// Little-endian unsigned 32-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<4>, mapper: U32LeMapper }`.
pub struct U32Le;

/// Big-endian unsigned 32-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<4>, mapper: U32BeMapper }`.
pub struct U32Be;

} // verus!
