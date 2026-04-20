//! Unsigned integer combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use vstd::prelude::*;

verus! {

/// Unsigned 8-bit integer combinator.
///
/// Defined as `Mapped { inner: Fixed::<1>, mapper: (u8_from_bytes, u8_to_bytes) }`.
pub struct U8;

/// Little-endian unsigned 16-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<2>, mapper: (u16_le_from_bytes, u16_le_to_bytes) }`.
pub struct U16Le;

/// Big-endian unsigned 16-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<2>, mapper: (u16_be_from_bytes, u16_be_to_bytes) }`.
pub struct U16Be;

/// Little-endian unsigned 32-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<4>, mapper: (u32_le_from_bytes, u32_le_to_bytes) }`.
pub struct U32Le;

/// Big-endian unsigned 32-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<4>, mapper: (u32_be_from_bytes, u32_be_to_bytes) }`.
pub struct U32Be;

impl LeafNonMalleable for U8 {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for U16Le {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for U16Be {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for U32Le {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for U32Be {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
