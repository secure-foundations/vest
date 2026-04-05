//! ASN.1 formats.
/// ASN.1 BOOLEAN.
pub mod bool;

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

/// Convenience value alias for the BER variant of ASN.1 BOOLEAN.
pub const BerBool: Bool<false> = Bool;

/// Convenience type alias for the DER variant of ASN.1 BOOLEAN.
pub type DerBool = Bool<true>;

/// Convenience value alias for the DER variant of ASN.1 BOOLEAN.
pub const DerBool: Bool<true> = Bool;

} // verus!
