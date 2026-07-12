#![allow(non_upper_case_globals)]

//! ASN.1 formats.

/// ASN.1 BIT STRING contents octets.
pub mod bitstring;
/// ASN.1 BMPString contents.
pub mod bmpstring;
/// ASN.1 BOOLEAN contents octet.
pub mod boolean;
/// Shared semantic date/time values and calendar operations.
pub mod datetime;
/// ASN.1 notation-style aliases for universal formats with DER encoding.
pub mod der;
/// ASN.1 GeneralizedTime contents.
pub mod generalizedtime;
/// ASN.1 IA5String contents.
pub mod ia5string;
/// ASN.1 INTEGER contents octets.
pub mod integer;
/// ASN.1 definite length octets.
pub mod length;
/// ASN.1 component modifiers: IMPLICIT, EXPLICIT, OPTIONAL, and DEFAULT.
pub mod modifiers;
/// ASN.1 PrintableString contents.
pub mod printablestring;
/// ASN.1 tag octets.
pub mod tag;
/// ASN.1 TeletexString contents.
pub mod teletexstring;
/// ASN.1 TLV wrapper.
pub mod tlv;
/// ASN.1 UTCTime contents.
pub mod utctime;
/// ASN.1 UTF8String contents.
pub mod utf8string;

pub use datetime::{DateTime, TimePrecision, TimeZone};
pub use der::*;
pub use generalizedtime::{GeneralizedTimeSpec, GeneralizedTimeValue};
pub use integer::{IntVal, Integer16, Integer8};
pub use modifiers::{ContextExplicit, ContextImplicit, Defaulted, Explicit, Implicit};
pub use tag::Tag;
pub use utctime::UtcTimeValue;

use crate::{
    combinators::{
        implicit::NBytesOf, mapped::spec::FnSpecMapper, Const, Empty, PrefixTagged, Tail, TryMap,
        U8,
    },
    core::proof::{Leaf, LeafNonMalleable},
};
use vstd::prelude::*;

verus! {

pub const DER: bool = true;

pub const BER: bool = false;

#[derive(Copy)]
pub struct ASN1<Content, const DER: bool = true>(pub Tag, pub Content);

impl<Content: Clone, const DER: bool> Clone for ASN1<Content, DER> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Content::clone, (&self.1,), cloned.1),
    {
        ASN1(self.0, self.1.clone())
    }
}

/// ASN.1 BOOLEAN format.
///
/// When `DER = true` (the default), this is the canonical DER form:
/// FALSE = `0x00`, TRUE = `0xFF`.
///
/// When `DER = false`, this is the more permissive BER form:
/// FALSE = `0x00`, TRUE = any non-zero byte.
#[derive(Clone, Copy)]
pub struct Bool<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 BOOLEAN.
pub type BerBool = Bool<false>;

/// Convenience type alias for the DER variant of ASN.1 BOOLEAN.
pub type DerBool = Bool<true>;

/// Convenience value alias for the BER variant of ASN.1 BOOLEAN.
pub const BerBool: Bool<false> = Bool;

/// Convenience value alias for the DER variant of ASN.1 BOOLEAN.
pub const DerBool: Bool<true> = Bool;

/// ASN.1 definite length format whose codomain is `nat`
#[derive(Clone, Copy)]
pub struct NatLength<const DER: bool = true>;

/// ASN.1 definite length format.
///
/// When `DER = true` (the default), only the canonical DER definite form is
/// accepted/produced.
///
/// When `DER = false`, the parser/serializer is BER-permissive over short and long
/// definite forms, without minimality constraints.
#[derive(Clone, Copy)]
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
#[derive(Clone, Copy)]
pub struct Integer;

/// ASN.1 BIT STRING contents format.
///
/// When `DER = true` (the default), only the canonical DER form is accepted, which requires
/// the trailing unused bits to be zero.
///
/// When `DER = false`, the parser allows any value for the trailing unused bits.
#[derive(Clone, Copy)]
pub struct BitStringFmt<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 BIT STRING.
pub type BerBitString = BitStringFmt<false>;

/// ASN.1 tag format combinator.
///
/// Only the canonical DER form is accepted:
/// - Tag numbers 0–30 must use the short (1-byte) form.
/// - High tag numbers must have no leading zero in the base-128 encoding.
#[derive(Clone, Copy)]
pub struct TagFmt;

/// Convenience type alias for the DER variant of ASN.1 BIT STRING.
pub type DerBitString = BitStringFmt<true>;

/// ASN.1 OCTET STRING contents format (primitive).
///
/// TODO: support indefinite (constructed) forms:
///
/// ### Example
///
/// 24 80 04 03 42 45 52 24 80 04 01 2D 04 05 52 55 4C 45 53 00 00 00 00
/// │  │  │  │  └───────┘ │  │  │  │  │  │  │  └──────────────┘ │     │
/// │  │  │  │  "BER"     │  │  │  │  │  │  └─ Len: 5 "RULES"   │     └─ Outer EOC
/// │  │  │  └─ Len: 3    │  │  │  │  │  └─ Primitive           └─ Inner EOC
/// │  │  └─ Primitive    │  │  │  │  └─ "-"
/// │  └─ Indefinite      │  │  │  └─ Len: 1
/// └─ Outer Outer        │  │  └─ Primitive
///                       │  └─ Indefinite
///                       └─ Inner Constructed
///
/// [TAG: 24] Constructed OCTET STRING (Indefinite Length)
///  │
///  ├── [TAG: 04] Primitive OCTET STRING (Definite Length: 3)
///  │      └── Value: "BER" (Hex: 42 45 52)
///  │
///  ├── [TAG: 24] Constructed OCTET STRING (Indefinite Length)
///  │      │
///  │      ├── [TAG: 04] Primitive OCTET STRING (Definite Length: 1)
///  │      │      └── Value: "-" (Hex: 2D)
///  │      │
///  │      ├── [TAG: 04] Primitive OCTET STRING (Definite Length: 5)
///  │      │      └── Value: "RULES" (Hex: 52 55 4C 45 53)
///  │      │
///  │      └── [TAG: 00] End-of-Contents (EOC) Marker (Hex: 00 00)
///  │             └── Meaning: Closes the Inner Constructed String
///  │
///  └── [TAG: 00] End-of-Contents (EOC) Marker (Hex: 00 00)
///         └── Meaning: Closes the Outer Constructed String
pub type OctetString = Tail;

/// Convenience value alias for ASN.1 OCTET STRING contents format.
pub const OctetString: Tail = Tail;

/// ASN.1 NULL format.
pub type Null = Empty;

/// Convenience value alias for ASN.1 NULL format.
pub const Null: Empty = Empty;

/// ASN.1 UTCTime format.
#[derive(Clone, Copy)]
pub struct UtcTime<const DER: bool = true>;

pub type BerUtcTime = UtcTime<false>;

pub type DerUtcTime = UtcTime<true>;

pub const BerUtcTime: BerUtcTime = UtcTime;

pub const DerUtcTime: DerUtcTime = UtcTime;

/// ASN.1 UTF8String format.
#[derive(Clone, Copy)]
pub struct Utf8String;

/// ASN.1 PrintableString format.
#[derive(Clone, Copy)]
pub struct PrintableString;

/// ASN.1 IA5String format.
#[derive(Clone, Copy)]
pub struct Ia5String;

/// ASN.1 BMPString format.
#[derive(Clone, Copy)]
pub struct BmpString;

/// ASN.1 TeletexString format.
#[derive(Clone, Copy)]
pub struct TeletexString;

/// ASN.1 GeneralizedTime format.
#[derive(Clone, Copy)]
pub struct GeneralizedTime<const DER: bool = true>;

pub type BerGeneralizedTime = GeneralizedTime<false>;

pub type DerGeneralizedTime = GeneralizedTime<true>;

pub const BerGeneralizedTime: BerGeneralizedTime = GeneralizedTime;

pub const DerGeneralizedTime: DerGeneralizedTime = GeneralizedTime;

impl LeafNonMalleable for DerBool {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl Leaf for BerBool {
    proof fn leaf_inv(&self) {
    }
}

// impl LeafNonMalleable for DerLength {
//     proof fn nonmal_leaf_inv(&self) {
//     }
// }
// impl Leaf for BerLength {
//     proof fn leaf_inv(&self) {
//     }
// }
} // verus!
