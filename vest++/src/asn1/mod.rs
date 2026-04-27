#![allow(non_upper_case_globals)]

//! ASN.1 formats.
pub(crate) mod base256;
/// ASN.1 BIT STRING contents octets.
pub mod bitstring;
/// ASN.1 BOOLEAN contents octet.
pub mod boolean;
/// ASN.1 INTEGER contents octets.
pub mod integer;
/// ASN.1 definite length octets.
pub mod length;

use crate::{
    combinators::{
        implicit::NBytesOf, mapped::spec::FnSpecMapper, Implicit, Tail, TryMap, WithPrefixTag, U8,
    },
    core::proof::{Leaf, LeafNonMalleable},
};
use vstd::prelude::*;

verus! {

pub enum ASN1Tag {
    Boolean = 0x01,
    Integer = 0x02,
    BitString = 0x03,
    OctetString = 0x04,
    // ...
}

pub type TagFmt = TryMap<U8, FnSpecMapper<u8, ASN1Tag>>;

pub type ASN1TLV<T, Len = usize> = WithPrefixTag<TagFmt, Implicit<Length, NBytesOf<Len, T>>>;

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
/// When `DER = false`, the parser/serializer is BER-permissive over short and long
/// definite forms, without minimality constraints.
pub struct Length<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 definite length.
pub type BerLength = Length<false>;

/// Convenience type alias for the DER variant of ASN.1 definite length.
pub type DerLength = Length<true>;

/// Convenience value alias for the BER variant of ASN.1 definite length.
pub const BerLength: Length<false> = Length;

/// Convenience value alias for the DER variant of ASN.1 definite length.
pub const DerLength: Length<true> = Length;

/// ASN.1 INTEGER contents format.
pub struct Integer;

/// ASN.1 BIT STRING contents format.
///
/// When `DER = true` (the default), only the canonical DER form is accepted, which requires
/// the trailing unused bits to be zero.
///
/// When `DER = false`, the parser allows any value for the trailing unused bits.
pub struct BitString<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 BIT STRING.
pub type BerBitString = BitString<false>;

/// Convenience type alias for the DER variant of ASN.1 BIT STRING.
pub type DerBitString = BitString<true>;

/// ASN.1 OCTET STRING contents format.
pub type OctetString = Tail;

/// Convenience value alias for ASN.1 OCTET STRING contents format.
pub const OctetString: Tail = Tail;

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
