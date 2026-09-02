//! BER restricted character string combinators.
use crate::asn1::{
    primitive_tag, ASN1Fmt, BmpStringFmt, Class, Ia5StringFmt, NumericStringFmt,
    PrintableStringFmt, Tag, TagFmt, TeletexStringFmt, UniversalStringFmt, Utf8StringFmt, BER,
};
#[cfg(feature = "alloc")]
use crate::asn1::{
    BmpString, Ia5StringOwned, NumericStringOwned, PrintableStringOwned, TeletexStringOwned,
    UniversalString, Utf8StringOwned,
};
use crate::combinators::{mapped::spec::FnSpecMapper, Mapped, Refined};
use crate::core::exec::parser::*;
use crate::core::exec::{
    ByteLen, OutputBuf, PResult, ParseError, Parser, PreSerializeError, Prepare, Serializer,
};
use crate::core::{proof::*, spec::*};
#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;

use super::octet_string::BerOctetStringFmt;

verus! {

type BerRestrictedStringFmt__<C, const LIMIT: usize> = Mapped<
    Refined<BerOctetStringFmt<LIMIT>, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, <C as SpecByteLen>::T>,
>;

/// reject invalid flattened contents, then map the validated octets to the string value.
pub open spec fn ber_char_string_fmt<C: SpecCombinator, const LIMIT: usize>(
    tag: Tag,
    content: C,
) -> BerRestrictedStringFmt__<C, LIMIT> {
    Mapped {
        inner: Refined(
            BerOctetStringFmt::<LIMIT>(tag),
            |bytes: Seq<u8>| content.spec_parse(bytes) is Some,
        ),
        mapper: (
            |bytes: Seq<u8>| (content.spec_parse(bytes)->0).1,
            |value: C::T| content.spec_serialize(value),
        ),
    }
}

/// BER restricted character string represented as an IMPLICITly tagged BER OCTET STRING.
///
/// Parsing accepts primitive, definite constructed, indefinite constructed, and nested forms.
/// Only the outermost tag is configurable; recursive components retain the universal OCTET STRING
/// tag. Serialization is normalized to primitive definite form.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Copy)]
pub struct BerCharStringFmt<C, const LIMIT: usize>(pub Tag, pub C);

mod derived_specs {
    use super::*;

    impl<C: SpecCombinator, const LIMIT: usize> SpecParser for BerCharStringFmt<C, LIMIT> {
        type PVal = C::T;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).spec_parse(ibuf)
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> Consistency for BerCharStringFmt<C, LIMIT> {
        type Val = C::T;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            &&& self.1.consistent(value)
            &&& ber_char_string_fmt::<C, LIMIT>(self.0, self.1).consistent(value)
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> SpecSerializerDps for BerCharStringFmt<C, LIMIT> {
        type SValue = C::T;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).spec_serialize_dps(value, obuf)
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> SpecSerializer for BerCharStringFmt<C, LIMIT> {
        type SVal = C::T;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).spec_serialize(value)
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> SpecByteLen for BerCharStringFmt<C, LIMIT> {
        type T = C::T;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<C: SpecCombinator, const LIMIT: usize> SafeParser for BerCharStringFmt<C, LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_parse_safe(ibuf);
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> Productive for BerCharStringFmt<C, LIMIT> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_productive(ibuf);
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> GoodSerializer for BerCharStringFmt<C, LIMIT> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_serialize_len(value);
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> NonTailFmt for BerCharStringFmt<C, LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_serialize_dps_prepend(
                value,
                obuf,
            );
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> EquivSerializersGeneral for BerCharStringFmt<
        C,
        LIMIT,
    > {
        proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_serialize_equiv(value, obuf);
        }
    }

    impl<C: SpecCombinator, const LIMIT: usize> EquivSerializers for BerCharStringFmt<C, LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            ber_char_string_fmt::<C, LIMIT>(self.0, self.1).lemma_serialize_equiv_on_empty(value);
        }
    }

    impl<C: SpecCombinator + SPRoundTrip, const LIMIT: usize> SPRoundTripDps for BerCharStringFmt<
        C,
        LIMIT,
    > {
        open spec fn unambiguous(&self) -> bool {
            self.1.sp_roundtrip_inv()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            let bytes = self.1.spec_serialize(value);
            self.1.theorem_serialize_parse_roundtrip(value);
            BerOctetStringFmt::<LIMIT>(self.0).theorem_serialize_dps_parse_roundtrip(bytes, obuf);
        }
    }

}

impl<C: Copy, const LIMIT: usize> BerCharStringFmt<C, LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn with_implicit_tag(content: C, class: Class, number: u64) -> Self
        returns
            Self(
                Tag {
                    class,
                    constructed: false,
                    number: crate::asn1::tag::tag_num_from_uint(number),
                },
                content,
            ),
    {
        Self(
            Tag { class, constructed: false, number: crate::asn1::tag::tag_num_from_uint(number) },
            content,
        )
    }
}

pub type BerUtf8StringFmt<const LIMIT: usize> = BerCharStringFmt<Utf8StringFmt, LIMIT>;

pub type BerPrintableStringFmt<const LIMIT: usize> = BerCharStringFmt<PrintableStringFmt, LIMIT>;

pub type BerIa5StringFmt<const LIMIT: usize> = BerCharStringFmt<Ia5StringFmt, LIMIT>;

pub type BerTeletexStringFmt<const LIMIT: usize> = BerCharStringFmt<TeletexStringFmt, LIMIT>;

pub type BerBmpStringFmt<const LIMIT: usize> = BerCharStringFmt<BmpStringFmt, LIMIT>;

pub type BerNumericStringFmt<const LIMIT: usize> = BerCharStringFmt<NumericStringFmt, LIMIT>;

pub type BerUniversalStringFmt<const LIMIT: usize> = BerCharStringFmt<UniversalStringFmt, LIMIT>;

impl<const LIMIT: usize> BerUtf8StringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::UTF8_STRING, Utf8StringFmt),
    {
        Self(TagFmt::UTF8_STRING, Utf8StringFmt)
    }

    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self::with_implicit_tag(Utf8StringFmt, class, number),
    {
        Self::with_implicit_tag(Utf8StringFmt, class, number)
    }
}

impl<const LIMIT: usize> BerPrintableStringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::PRINTABLE_STRING, PrintableStringFmt),
    {
        Self(TagFmt::PRINTABLE_STRING, PrintableStringFmt)
    }

    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self::with_implicit_tag(PrintableStringFmt, class, number),
    {
        Self::with_implicit_tag(PrintableStringFmt, class, number)
    }
}

impl<const LIMIT: usize> BerIa5StringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::IA5_STRING, Ia5StringFmt),
    {
        Self(TagFmt::IA5_STRING, Ia5StringFmt)
    }

    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self::with_implicit_tag(Ia5StringFmt, class, number),
    {
        Self::with_implicit_tag(Ia5StringFmt, class, number)
    }
}

impl<const LIMIT: usize> BerTeletexStringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::TELETEX_STRING, TeletexStringFmt),
    {
        Self(TagFmt::TELETEX_STRING, TeletexStringFmt)
    }

    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self::with_implicit_tag(TeletexStringFmt, class, number),
    {
        Self::with_implicit_tag(TeletexStringFmt, class, number)
    }
}

impl<const LIMIT: usize> BerBmpStringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::BMP_STRING, BmpStringFmt),
    {
        Self(TagFmt::BMP_STRING, BmpStringFmt)
    }

    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self::with_implicit_tag(BmpStringFmt, class, number),
    {
        Self::with_implicit_tag(BmpStringFmt, class, number)
    }
}

impl<const LIMIT: usize> BerNumericStringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::NUMERIC_STRING, NumericStringFmt),
    {
        Self(TagFmt::NUMERIC_STRING, NumericStringFmt)
    }
}

impl<const LIMIT: usize> BerUniversalStringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::UNIVERSAL_STRING, UniversalStringFmt),
    {
        Self(TagFmt::UNIVERSAL_STRING, UniversalStringFmt)
    }
}

/// Executable bridge from owned BER contents octets to owned values.
#[cfg(feature = "alloc")]
pub trait BerDecoderOwned: SpecCombinator {
    type Owned: DeepView<V = Self::T>;

    fn decode_owned(&self, bytes: Vec<u8>) -> (r: Result<Self::Owned, ParseError>)
        ensures
            ({
                let expected = match self.spec_parse(bytes.deep_view()) {
                    Some((_, value)) => Some(value),
                    None => None,
                };
                &&& r is Ok <==> expected is Some
                &&& r is Err <==> expected is None
                &&& r matches Ok(value) ==> expected == Some(value.deep_view())
            }),
    ;
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for Utf8StringFmt {
    type Owned = Utf8StringOwned;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        let input = bytes.as_slice();
        if crate::asn1::utf8string::is_valid_utf8(input) {
            // SAFETY: the branch condition establishes that `bytes` is valid UTF-8.
            let inner = unsafe { String::from_utf8_unchecked(bytes) };
            Ok(inner)
        } else {
            Err(ParseError::custom("Invalid UTF-8"))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for PrintableStringFmt {
    type Owned = PrintableStringOwned;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        broadcast use vstd::utf8::decode_utf8_encode_utf8;

        let input = bytes.as_slice();
        if !crate::asn1::printablestring::is_valid_printable_string(input) {
            Err(ParseError::custom("Invalid PrintableString"))
        } else if !crate::asn1::utf8string::is_valid_utf8(input) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            // SAFETY: the preceding check establishes that `bytes` is valid UTF-8.
            let inner = unsafe { String::from_utf8_unchecked(bytes) };
            Ok(PrintableStringOwned::new(inner))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for NumericStringFmt {
    type Owned = NumericStringOwned;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        let value = <PrintableStringFmt as BerDecoderOwned>::decode_owned(
            &PrintableStringFmt,
            bytes,
        )?;
        if crate::core::exec::fns::Pred::test(
            &crate::asn1::numericstring::NumericStringChars,
            &value,
        ) {
            Ok(value)
        } else {
            Err(ParseError::custom("Invalid NumericString"))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for UniversalStringFmt {
    type Owned = UniversalString;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        if crate::asn1::universalstring::check_valid_universal_string(bytes.as_slice()) {
            Ok(crate::asn1::universalstring::decode_universal_string_owned(bytes.as_slice()))
        } else {
            Err(ParseError::custom("Invalid UniversalString"))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for Ia5StringFmt {
    type Owned = Ia5StringOwned;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        broadcast use vstd::utf8::decode_utf8_encode_utf8;

        let input = bytes.as_slice();
        if !crate::asn1::ia5string::is_valid_ia5_string(input) {
            Err(ParseError::custom("Invalid IA5String"))
        } else if !crate::asn1::utf8string::is_valid_utf8(input) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            // SAFETY: the preceding check establishes that `bytes` is valid UTF-8.
            let inner = unsafe { String::from_utf8_unchecked(bytes) };
            Ok(Ia5StringOwned::new(inner))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for TeletexStringFmt {
    type Owned = TeletexStringOwned;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        broadcast use vstd::utf8::decode_utf8_encode_utf8;

        let input = bytes.as_slice();
        if !crate::asn1::teletexstring::is_valid_teletex_string(input) {
            Err(ParseError::custom("Invalid TeletexString"))
        } else if !crate::asn1::utf8string::is_valid_utf8(input) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            // SAFETY: the preceding check establishes that `bytes` is valid UTF-8.
            let inner = unsafe { String::from_utf8_unchecked(bytes) };
            Ok(TeletexStringOwned::new(inner))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for BmpStringFmt {
    type Owned = BmpString;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        assert(bytes@ == bytes.deep_view());
        let (_, parsed) = BmpStringFmt.parse(&bytes.as_slice())?;
        Ok(parsed)
    }
}

#[cfg(feature = "alloc")]
impl<'i, C, const LIMIT: usize> Parser<&'i [u8]> for BerCharStringFmt<C, LIMIT> where
    C: BerDecoderOwned,
 {
    type PT = C::Owned;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = BerOctetStringFmt::<LIMIT>(self.0).parse(ibuf)?;
        let value = self.1.decode_owned(bytes)?;
        Ok((n, value))
    }
}

impl<Output, C, T, const LIMIT: usize> Serializer<Output, T> for BerCharStringFmt<C, LIMIT> where
    Output: OutputBuf,
    T: DeepView + ?Sized,
    C: SpecCombinator + Copy + GoodSerializer + Serializer<Output, T> + ByteLen<T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& <C as Serializer<Output, T>>::exec_inv(&self.1)
        &&& <C as ByteLen<T>>::exec_inv(&self.1)
        &&& self.1.serialize_inv()
    }

    fn serialize_into(&self, value: &T, obuf: &mut Output) {
        proof {
            self.1.lemma_serialize_len(value.deep_view());
        }
        let normalized = ASN1Fmt::<C, BER>(primitive_tag(self.0), self.1);
        normalized.serialize_into(value, obuf);
    }
}

impl<C, T, const LIMIT: usize> Prepare<T> for BerCharStringFmt<C, LIMIT> where
    T: DeepView + ?Sized,
    C: SpecCombinator + Copy + GoodSerializer + SPRoundTrip + Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& <C as Prepare<T>>::exec_inv(&self.1)
        &&& self.1.serialize_inv()
        &&& self.1.sp_roundtrip_inv()
    }

    fn prepare(&self, value: &T) -> Result<usize, PreSerializeError> {
        let normalized = ASN1Fmt::<C, BER>(primitive_tag(self.0), self.1);
        let result = normalized.prepare(value);
        proof {
            if let Ok(_len) = result {
                self.1.lemma_serialize_len(value.deep_view());
                self.1.theorem_serialize_parse_roundtrip(value.deep_view());
            }
        }
        result
    }
}

impl<C, T, const LIMIT: usize> ByteLen<T> for BerCharStringFmt<C, LIMIT> where
    T: DeepView + ?Sized,
    C: SpecCombinator + Copy + GoodSerializer + ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as ByteLen<T>>::exec_inv(&self.1) && self.1.serialize_inv()
    }

    fn length(&self, value: &T) -> usize {
        proof {
            self.1.lemma_serialize_len(value.deep_view());
        }
        let normalized = ASN1Fmt::<C, BER>(primitive_tag(self.0), self.1);
        normalized.length(value)
    }
}

} // verus!
