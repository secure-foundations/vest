//! Fixed-width signed integer combinators.
//!
//! These parse and serialize two's-complement integers in explicit little- or
//! big-endian byte order.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use vstd::prelude::*;

verus! {

/// Signed 8-bit integer combinator.
///
/// Defined as `Mapped { inner: Fixed::<1>, mapper: (i8_from_bytes, i8_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I8;

/// Little-endian signed 16-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<2>, mapper: (i16_le_from_bytes, i16_le_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I16Le;

/// Big-endian signed 16-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<2>, mapper: (i16_be_from_bytes, i16_be_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I16Be;

/// Little-endian signed 32-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<4>, mapper: (i32_le_from_bytes, i32_le_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I32Le;

/// Big-endian signed 32-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<4>, mapper: (i32_be_from_bytes, i32_be_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I32Be;

/// Little-endian signed 64-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<8>, mapper: (i64_le_from_bytes, i64_le_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I64Le;

/// Big-endian signed 64-bit integer.
///
/// Defined as `Mapped { inner: Fixed::<8>, mapper: (i64_be_from_bytes, i64_be_to_bytes) }`.
#[derive(Clone, Copy)]
pub struct I64Be;

impl LeafNonMalleable for I8 {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for I16Le {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for I16Be {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for I32Le {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for I32Be {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for I64Le {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl LeafNonMalleable for I64Be {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
