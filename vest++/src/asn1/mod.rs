//! ASN.1 formats.
pub(crate) mod base256;
/// ASN.1 BOOLEAN.
pub mod boolean;
/// ASN.1 INTEGER contents octets.
pub mod integer;
/// ASN.1 definite length octets.
pub mod length;

use crate::core::proof::{Leaf, LeafNonMalleable};
use vstd::prelude::*;

verus! {

/// ASN.1 BOOLEAN format.
///
/// When `DER = true` (the default), this is the canonical DER form:
/// FALSE = `0x00`, TRUE = `0xFF`.
///
/// When `DER = false`, this is the more permissive BER form:
/// FALSE = `0x00`, TRUE = any non-zero byte.
pub struct Bool<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 BOOLEAN.
pub type BerBool = Bool<false>;

/// Convenience type alias for the DER variant of ASN.1 BOOLEAN.
pub type DerBool = Bool<true>;

/// Convenience value alias for the BER variant of ASN.1 BOOLEAN.
pub const BerBool: Bool<false> = Bool;

/// Convenience value alias for the DER variant of ASN.1 BOOLEAN.
pub const DerBool: Bool<true> = Bool;

/// ASN.1 definite length format.
///
/// When `DER = true` (the default), only the canonical DER definite form is
/// accepted/produced.
///
/// When `DER = false`, the parser is BER-permissive over short and long
/// definite forms, while serialization remains canonical.
pub struct Length<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 definite length.
pub type BerLength = Length<false>;

/// Convenience type alias for the DER variant of ASN.1 definite length.
pub type DerLength = Length<true>;

/// Convenience value alias for the BER variant of ASN.1 definite length.
pub const BerLength: Length<false> = Length;

/// Convenience value alias for the DER variant of ASN.1 definite length.
pub const DerLength: Length<true> = Length;

/// ASN.1 INTEGER contents format with externally supplied contents length.
pub struct Integer<Len = usize>(pub Len);

impl LeafNonMalleable for DerBool {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl Leaf for BerBool {
    proof fn leaf_inv(&self) {
    }
}

impl LeafNonMalleable for DerLength {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl Leaf for BerLength {
    proof fn leaf_inv(&self) {
    }
}

} // verus!
