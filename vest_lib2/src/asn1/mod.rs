#![allow(non_upper_case_globals)]

//! ASN.1 formats.

/// ASN.1 ANY / open-type complete TLV format.
pub mod any;
/// BER indefinite-length and constructed-value combinators.
pub mod ber;
/// ASN.1 BIT STRING contents octets.
pub mod bitstring;
/// ASN.1 BMPString contents.
pub mod bmpstring;
/// ASN.1 BOOLEAN contents octet.
pub mod boolean;
/// Reusable ASN.1 subtype-constraint predicates.
pub mod constraints;
/// Shared semantic date/time values and calendar operations.
pub mod datetime;
/// ASN.1 notation-style aliases for universal formats with DER encoding.
pub mod der;
/// Disjointness proofs for complete ASN.1 formats.
pub mod disjoint;
/// ASN.1 ENUMERATED contents octets.
pub mod enumerated;
/// ASN.1 GeneralizedTime contents.
pub mod generalizedtime;
/// ASN.1 IA5String contents.
pub mod ia5string;
/// ASN.1 INTEGER contents octets.
pub mod integer;
/// ASN.1 definite length octets.
pub mod length;
/// Shared ASN.1 tagging and component modifiers.
pub mod modifiers;
/// ASN.1 OBJECT IDENTIFIER contents octets.
pub mod oid;
/// ASN.1 PrintableString contents.
pub mod printablestring;
/// ASN.1 REAL contents octets.
pub mod real;
/// ASN.1 DER SET OF contents.
pub mod set_of;
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

#[cfg(feature = "alloc")]
pub use any::AnyOwned;
pub use any::{Any, AnySpec};
pub use ber::{
    BerAnyFmt, BerBitStringFmt, BerBmpStringFmt, BerCharStringFmt, BerIa5StringFmt,
    BerOctetStringFmt, BerPrintableStringFmt, BerSequenceFmt, BerSequenceOfFmt,
    BerTeletexStringFmt, BerUtf8StringFmt, EocFmt, EOC,
};
#[cfg(feature = "alloc")]
pub use bitstring::BitStringOwned;
pub use bitstring::{BitString, BitStringSpec};
#[cfg(feature = "alloc")]
pub use bmpstring::BmpString;
pub use bmpstring::BmpStringSpec;
pub use constraints::{ConstraintAnd, ConstraintNot, ConstraintOr, IntegerRange, Size};
pub use datetime::{DateTime, TimePrecision, TimeZone};
pub use der::*;
pub use enumerated::Enumerated;
pub use generalizedtime::{GeneralizedTime, GeneralizedTimeSpec};
#[cfg(feature = "alloc")]
pub use ia5string::Ia5StringOwned;
pub use ia5string::{Ia5String, Ia5StringSpec};
pub use integer::{Integer, Integer16Fmt, Integer8Fmt};
pub use modifiers::{DefaultedFmt, ImplicitlyTaggedFmt, Retaggable};
#[cfg(feature = "alloc")]
pub use oid::ObjectIdentifier;
pub use oid::ObjectIdentifierSpec;
#[cfg(feature = "alloc")]
pub use printablestring::PrintableStringOwned;
pub use printablestring::{PrintableString, PrintableStringSpec};
pub use real::{Real, RealSpec};
pub use set_of::{DerOrd, SetOfFmt};
pub use tag::{constructed_tag, primitive_tag, Class, Tag};
#[cfg(feature = "alloc")]
pub use teletexstring::TeletexStringOwned;
pub use teletexstring::{TeletexString, TeletexStringSpec};
pub use utctime::UtcTime;
pub use utf8string::Utf8String;
#[cfg(feature = "alloc")]
pub use utf8string::Utf8StringOwned;

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
pub struct ASN1Fmt<Content, const DER: bool = true>(pub Tag, pub Content);

impl<Content: Clone, const DER: bool> Clone for ASN1Fmt<Content, DER> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Content::clone, (&self.1,), cloned.1),
    {
        ASN1Fmt(self.0, self.1.clone())
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
pub struct BoolFmt<const DER: bool = true>;

/// Convenience type alias for the BER variant of ASN.1 BOOLEAN.
pub type BerBoolFmt = BoolFmt<false>;

/// Convenience type alias for the DER variant of ASN.1 BOOLEAN.
pub type DerBoolFmt = BoolFmt<true>;

/// Convenience value alias for the BER variant of ASN.1 BOOLEAN.
pub const BerBoolFmt: BoolFmt<false> = BoolFmt;

/// Convenience value alias for the DER variant of ASN.1 BOOLEAN.
pub const DerBoolFmt: BoolFmt<true> = BoolFmt;

/// ASN.1 ANY/open-type format.
///
/// Unlike the content markers in this module, `AnyFmt` parses and serializes one complete
/// tag-length-value encoding.
#[derive(Clone, Copy)]
pub struct AnyFmt<const DER: bool = true>;

/// Definite-length-only BER ANY format.
///
/// Prefer [`ber::BerAnyFmt`] when indefinite constructed open values must be accepted.
pub type BerDefiniteAnyFmt = AnyFmt<false>;

pub type DerAnyFmt = AnyFmt<true>;

pub const BerDefiniteAnyFmt: BerDefiniteAnyFmt = AnyFmt;

pub const DerAnyFmt: DerAnyFmt = AnyFmt;

/// ASN.1 definite length format whose codomain is `nat`
#[derive(Clone, Copy)]
pub struct NatLengthFmt<const DER: bool = true>;

/// ASN.1 definite length format.
///
/// When `DER = true` (the default), only the canonical DER definite form is
/// accepted/produced.
///
/// When `DER = false`, the parser/serializer is BER-permissive over short and long
/// definite forms, without minimality constraints.
#[derive(Clone, Copy)]
pub struct LengthFmt<const DER: bool = true>;

/// BER length, including the indefinite form (`0x80`).
#[derive(StructuralEq, Copy, Clone, PartialEq, Eq, Debug)]
pub enum BerLength {
    Definite(usize),
    Indefinite,
}

impl DeepView for BerLength {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/// BER length determinant accepting both definite and indefinite encodings.
#[derive(Clone, Copy)]
pub struct BerLengthFmt;

/// ASN.1 INTEGER contents format.
#[derive(Clone, Copy)]
pub struct IntegerFmt;

/// ASN.1 ENUMERATED contents format.
#[derive(Clone, Copy)]
pub struct EnumeratedFmt;

/// ASN.1 OBJECT IDENTIFIER contents format.
#[derive(Clone, Copy)]
pub struct ObjectIdentifierFmt;

/// ASN.1 DER REAL contents format.
#[derive(Clone, Copy)]
pub struct RealFmt;

/// ASN.1 BIT STRING contents format.
///
/// When `DER = true` (the default), only the canonical DER form is accepted, which requires
/// the trailing unused bits to be zero.
///
/// When `DER = false`, the parser allows any value for the trailing unused bits.
#[derive(Clone, Copy)]
pub struct BitStringFmt<const DER: bool = true>;

/// Convenience type alias for primitive BER BIT STRING contents.
pub type BerBitStringContentFmt = BitStringFmt<false>;

/// ASN.1 tag format combinator.
///
/// Only the canonical DER form is accepted:
/// - Tag numbers 0–30 must use the short (1-byte) form.
/// - High tag numbers must have no leading zero in the base-128 encoding.
#[derive(Clone, Copy)]
pub struct TagFmt;

/// Convenience type alias for the DER variant of ASN.1 BIT STRING.
pub type DerBitStringFmt = BitStringFmt<true>;

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
pub type OctetStringFmt = Tail;

/// Convenience value alias for ASN.1 OCTET STRING contents format.
pub const OctetStringFmt: Tail = Tail;

/// ASN.1 NULL format.
pub type NullFmt = Empty;

/// Convenience value alias for ASN.1 NULL format.
pub const NullFmt: Empty = Empty;

/// ASN.1 UTCTime format.
#[derive(Clone, Copy)]
pub struct UtcTimeFmt<const DER: bool = true>;

pub type BerUtcTimeFmt = UtcTimeFmt<false>;

pub type DerUtcTimeFmt = UtcTimeFmt<true>;

pub const BerUtcTimeFmt: BerUtcTimeFmt = UtcTimeFmt;

pub const DerUtcTimeFmt: DerUtcTimeFmt = UtcTimeFmt;

/// ASN.1 UTF8String format.
#[derive(Clone, Copy)]
pub struct Utf8StringFmt;

/// ASN.1 PrintableString format.
#[derive(Clone, Copy)]
pub struct PrintableStringFmt;

/// ASN.1 IA5String format.
#[derive(Clone, Copy)]
pub struct Ia5StringFmt;

/// ASN.1 BMPString format.
#[derive(Clone, Copy)]
pub struct BmpStringFmt;

/// ASN.1 TeletexString format.
#[derive(Clone, Copy)]
pub struct TeletexStringFmt;

/// ASN.1 GeneralizedTime format.
#[derive(Clone, Copy)]
pub struct GeneralizedTimeFmt<const DER: bool = true>;

pub type BerGeneralizedTimeFmt = GeneralizedTimeFmt<false>;

pub type DerGeneralizedTimeFmt = GeneralizedTimeFmt<true>;

pub const BerGeneralizedTimeFmt: BerGeneralizedTimeFmt = GeneralizedTimeFmt;

pub const DerGeneralizedTimeFmt: DerGeneralizedTimeFmt = GeneralizedTimeFmt;

impl LeafNonMalleable for DerBoolFmt {
    proof fn nonmal_leaf_inv(&self) {
    }
}

impl Leaf for BerBoolFmt {
    proof fn leaf_inv(&self) {
    }
}

// impl LeafNonMalleable for DerLengthFmt {
//     proof fn nonmal_leaf_inv(&self) {
//     }
// }
// impl Leaf for BerLengthFmt {
//     proof fn leaf_inv(&self) {
//     }
// }
} // verus!
