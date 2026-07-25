//! BER constructed-value formats and notation-style aliases.
use crate::asn1::{
    ASN1Fmt, BerLength, BerLengthFmt, BitStringFmt, BmpStringFmt, BoolFmt, Class, EnumeratedFmt,
    Ia5StringFmt, IntegerFmt, NullFmt, ObjectIdentifierFmt, OctetStringFmt, PrintableStringFmt,
    RealFmt, Tag, TagFmt, TeletexStringFmt, Utf8StringFmt, BER,
};
#[cfg(feature = "alloc")]
use crate::asn1::{
    BmpString, Ia5StringOwned, PrintableStringOwned, TeletexStringOwned, Utf8StringOwned,
};
use crate::combinators::{
    bytes::ExactLen,
    mapped::spec::FnSpecMapper,
    recursive::{
        BundledSpecs, EquivSerializersGeneralRecBody, GoodSerializerRecBody, ParamRecSpecs,
        ParserRecBody, ProductiveRecBody, SafeParserRecBody, SpecRecBody,
    },
    Bind, Const, Empty, FixWith, Mapped, Pair, PrefixTagged, Refined, Repeat, RepeatTillEnd, Sum,
    Void, U8,
};
use crate::core::exec::fns::*;
use crate::core::exec::parser::*;
use crate::core::exec::{
    input::InputBuf, ByteLen, OutputBuf, PResult, ParseError, Parser, PreSerializeError, Prepare,
    Serializer,
};
use crate::core::{proof::*, spec::*};
use crate::Never;
#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(feature = "alloc")]
use vstd::slice::slice_to_vec;

use super::modifiers::{defaulted, explicit_tag};
pub use super::modifiers::{
    implicitly_tagged as Implicit, ImplicitFmt, CHOICE, IMPLICIT, IMPLICIT_APPLICATION,
    IMPLICIT_PRIVATE, OPTIONAL, REQUIRED,
};
use super::{AnyFmt, GeneralizedTimeFmt, Integer16Fmt, Integer8Fmt, LengthFmt, UtcTimeFmt};
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

/// Exact BER end-of-contents marker (`00 00`).
pub type EocFmt = Pair<Const<U8, u8>, Const<U8, u8>>;

/// Exact BER end-of-contents marker (`00 00`).
pub const EOC: EocFmt = Pair(Const(U8, 0u8), Const(U8, 0u8));

/// End marker for a schema-defined BER constructed value.
pub type BerEndFmt = Empty;

/// Generated SEQUENCE field chains can end in `Eof` for both DER and BER by importing the
/// encoding-rule module's notation.
pub type Eof = BerEndFmt;

#[allow(non_upper_case_globals)]
pub const Eof: Eof = Empty;

type BerSequenceWireType<T> = (BerLength, Sum<T, (T, (u8, u8))>);

type BerSequenceFmt__<C> = Mapped<
    PrefixTagged<
        TagFmt,
        Tag,
        Bind<BerLengthFmt, spec_fn(BerLength) -> Sum<ExactLen<C, usize>, Pair<C, EocFmt>>>,
    >,
    FnSpecMapper<BerSequenceWireType<<C as SpecByteLen>::T>, <C as SpecByteLen>::T>,
>;

/// BER `SEQUENCE` accepting definite and indefinite outer length forms.
///
/// The schema-specific `content` format parses the sequence components. Definite contents are
/// bounded by [`ExactLen`], while indefinite contents are followed by [`EOC`]. Serialization is
/// normalized to the definite form.
pub open spec fn ber_sequence_fmt<C: SpecCombinator>(tag: Tag, content: C) -> BerSequenceFmt__<C> {
    #[verusfmt::skip]
    Mapped {
        inner: PrefixTagged(TagFmt, tag, Bind(BerLengthFmt, |len: BerLength|
                match len {
                    BerLength::Definite(len) => L(ExactLen(len, content)),
                    BerLength::Indefinite => R(Pair(content, EOC)),
                },
            ),
        ),
        mapper: (
            |parsed: BerSequenceWireType<C::T>|
                match parsed.1 {
                    L(value) => value,
                    R((value, _eoc)) => value,
                },
            |value: C::T|
                {
                    let len = content.byte_len(value) as usize;
                    (BerLength::Definite(len), L(value))
                },
        ),
    }
}

/// The definite-length BER encoding selected by [`BerSequenceFmt`]'s serializer.
pub open spec fn ber_sequence_normalized_fmt<C>(tag: Tag, content: C) -> ASN1Fmt<C, BER> {
    ASN1Fmt(tag, content)
}

/// BER `SEQUENCE` codec with a configurable outer tag.
///
/// Parsing accepts either a definite-length schema body or the same body followed by [`EOC`]
/// under indefinite-length framing. Serialization always emits definite-length BER.
#[derive(Copy)]
pub struct BerSequenceFmt<C>(pub Tag, pub C);

impl<C: Clone> Clone for BerSequenceFmt<C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            cloned.0 == self.0,
            call_ensures(C::clone, (&self.1,), cloned.1),
    {
        BerSequenceFmt(self.0, self.1.clone())
    }
}

impl<C: Copy> BerSequenceFmt<C> {
    /// Ordinary universal `SEQUENCE`.
    #[verifier::allow_in_spec]
    pub const fn universal(content: C) -> Self
        returns
            Self(TagFmt::SEQUENCE, content),
    {
        Self(TagFmt::SEQUENCE, content)
    }

    /// An IMPLICIT-tagged `SEQUENCE`.
    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64, content: C) -> Self
        returns
            Self(
                Tag { class, constructed: true, number: super::tag::tag_num_from_uint(number) },
                content,
            ),
    {
        Self(
            Tag { class, constructed: true, number: super::tag::tag_num_from_uint(number) },
            content,
        )
    }
}

mod sequence_specs {
    use super::*;

    impl<C: SpecCombinator> SpecParser for BerSequenceFmt<C> {
        type PVal = C::T;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ber_sequence_fmt(self.0, self.1).spec_parse(ibuf)
        }
    }

    impl<C: SpecCombinator> Consistency for BerSequenceFmt<C> {
        type Val = C::T;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            ber_sequence_fmt(self.0, self.1).consistent(value)
        }
    }

    impl<C: SpecCombinator> SpecSerializerDps for BerSequenceFmt<C> {
        type SValue = C::T;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ber_sequence_fmt(self.0, self.1).spec_serialize_dps(value, obuf)
        }
    }

    impl<C: SpecCombinator> SpecSerializer for BerSequenceFmt<C> {
        type SVal = C::T;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_sequence_fmt(self.0, self.1).spec_serialize(value)
        }
    }

    impl<C: SpecCombinator> SpecByteLen for BerSequenceFmt<C> {
        type T = C::T;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            ber_sequence_fmt(self.0, self.1).byte_len(value)
        }
    }

}

mod sequence_proofs {
    use super::*;

    impl<C: SpecCombinator + SafeParser> SafeParser for BerSequenceFmt<C> {
        open spec fn safe_inv(&self) -> bool {
            self.1.safe_inv()
        }

        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_parse_safe(ibuf);
        }
    }

    impl<C: SpecCombinator + SafeParser + Productive> Productive for BerSequenceFmt<C> {
        open spec fn productive_inv(&self) -> bool {
            &&& self.1.safe_inv()
            &&& self.1.productive_inv()
        }

        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_productive(ibuf);
        }
    }

    impl<C: SpecCombinator + GoodSerializer> GoodSerializer for BerSequenceFmt<C> {
        open spec fn serialize_inv(&self) -> bool {
            self.1.serialize_inv()
        }

        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            ber_sequence_fmt(self.0, self.1).lemma_serialize_len(value);
        }
    }

    impl<C: SpecCombinator + GoodSerializer + EquivSerializers> NonTailFmt for BerSequenceFmt<C> {
        open spec fn serialize_dps_inv(&self) -> bool {
            &&& self.1.serialize_inv()
            &&& self.1.equiv_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_sequence_normalized_fmt(self.0, self.1).lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_sequence_normalized_fmt(self.0, self.1).lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<C: SpecCombinator + EquivSerializers> EquivSerializersGeneral for BerSequenceFmt<C> {
        open spec fn equiv_general_inv(&self) -> bool {
            self.1.equiv_inv()
        }

        proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
            ber_sequence_normalized_fmt(self.0, self.1).lemma_serialize_equiv(value, obuf);
        }
    }

    impl<C: SpecCombinator + EquivSerializers> EquivSerializers for BerSequenceFmt<C> {
        open spec fn equiv_inv(&self) -> bool {
            self.1.equiv_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<C> SPRoundTripDps for BerSequenceFmt<C> where
        C: SpecCombinator + GoodSerializer + EquivSerializers + NonTailFmt + SPRoundTripDps,
     {
        open spec fn unambiguous(&self) -> bool {
            &&& self.1.sp_roundtrip_inv()
            &&& self.1.serialize_dps_inv()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

}

impl<'i, C> Parser<&'i [u8]> for BerSequenceFmt<C> where
    C: SpecCombinator + Parser<&'i [u8]> + SafeParser + Copy,
 {
    type PT = C::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use super::tag::lemma_const_tag_fmt_exec_inv;

        let _ = ibuf.len();
        let (tag_len, _tag) = Const(TagFmt, self.0).parse(ibuf)?;
        let after_tag = ibuf.skip(tag_len);
        let (length_len, length) = BerLengthFmt.parse(&after_tag)?;
        let content = after_tag.skip(length_len);

        let (content_len, value) = match length {
            BerLength::Definite(len) => ExactLen(len, self.1).parse(&content)?,
            BerLength::Indefinite => {
                let (n, (value, _eoc)) = Pair(self.1, EOC).parse(&content)?;
                (n, value)
            },
        };
        let total = tag_len + length_len + content_len;
        assert(self.spec_parse(ibuf@) == Some((total as int, value.deep_view())));
        Ok((total, value))
    }
}

impl<Output: OutputBuf, C, T> Serializer<Output, T> for BerSequenceFmt<C> where
    T: DeepView + ?Sized,
    C: SpecCombinator + Serializer<Output, T> + ByteLen<T> + Copy,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& <C as Serializer<Output, T>>::exec_inv(&self.1)
        &&& <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn serialize_into(&self, value: &T, obuf: &mut Output) {
        let normalized = ASN1Fmt::<_, BER>(self.0, self.1);
        normalized.serialize_into(value, obuf);
    }
}

impl<C, T> Prepare<T> for BerSequenceFmt<C> where
    T: DeepView + ?Sized,
    C: SpecCombinator + Prepare<T> + Copy,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as Prepare<T>>::exec_inv(&self.1)
    }

    fn prepare(&self, value: &T) -> Result<usize, PreSerializeError> {
        let normalized = ASN1Fmt::<_, BER>(self.0, self.1);
        normalized.prepare(value)
    }
}

impl<C, T> ByteLen<T> for BerSequenceFmt<C> where
    T: DeepView + ?Sized,
    C: SpecCombinator + ByteLen<T> + Copy,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn length(&self, value: &T) -> usize {
        let normalized = ASN1Fmt::<_, BER>(self.0, self.1);
        normalized.length(value)
    }
}

type BerSequenceOfWireType<T> = (BerLength, Sum<Seq<T>, (Seq<T>, (u8, u8))>);

type BerSequenceOfInnerFmt<C> = Mapped<
    PrefixTagged<
        TagFmt,
        Tag,
        Bind<
            BerLengthFmt,
            spec_fn(BerLength) -> Sum<ExactLen<RepeatTillEnd<C>, usize>, Repeat<C, EocFmt>>,
        >,
    >,
    FnSpecMapper<BerSequenceOfWireType<<C as SpecByteLen>::T>, Seq<<C as SpecByteLen>::T>>,
>;

/// BER `SEQUENCE OF` accepting definite and indefinite outer length forms.
///
/// The indefinite branch is non-recursive at this layer: [`Repeat`] parses complete ASN.1
/// elements until [`EOC`]. Nested indefinite values are handled by the element codec itself.
/// Serialization is normalized to the definite form.
pub open spec fn ber_sequence_of_fmt<C: SpecCombinator>(
    tag: Tag,
    content: C,
) -> BerSequenceOfInnerFmt<C> {
    #[verusfmt::skip]
    Mapped {
        inner: PrefixTagged(TagFmt, tag, Bind(BerLengthFmt, |len: BerLength|
                match len {
                    BerLength::Definite(len) => L(ExactLen(len, RepeatTillEnd(content))),
                    BerLength::Indefinite => R(Repeat(content, EOC)),
                },
            ),
        ),
        mapper: (
            |parsed: BerSequenceOfWireType<C::T>|
                match parsed.1 {
                    L(values) => values,
                    R((values, _eoc)) => values,
                },
            |values: Seq<C::T>|
                {
                    let len = RepeatTillEnd(content).byte_len(values) as usize;
                    (BerLength::Definite(len), L(values))
                },
        ),
    }
}

/// The definite-length BER encoding selected by [`BerSequenceOfFmt`]'s serializer.
pub open spec fn ber_sequence_of_normalized_fmt<C>(tag: Tag, content: C) -> ASN1Fmt<
    RepeatTillEnd<C>,
    BER,
> {
    ASN1Fmt(tag, RepeatTillEnd(content))
}

/// BER `SEQUENCE OF` codec with a configurable outer tag.
///
/// Parsing accepts either a definite-length contents or an indefinite-length sequence
/// terminated by [`EOC`]. Each element must be a productive, complete ASN.1 TLV; in particular,
/// its parser must not accept [`EOC`] as an element. Serialization always emits definite-length BER.
#[derive(Copy)]
pub struct BerSequenceOfFmt<C>(pub Tag, pub C);

impl<C: Clone> Clone for BerSequenceOfFmt<C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            cloned.0 == self.0,
            call_ensures(C::clone, (&self.1,), cloned.1),
    {
        BerSequenceOfFmt(self.0, self.1.clone())
    }
}

impl<C: Copy> BerSequenceOfFmt<C> {
    /// Ordinary universal `SEQUENCE OF`.
    #[verifier::allow_in_spec]
    pub const fn universal(content: C) -> Self
        returns
            Self(TagFmt::SEQUENCE, content),
    {
        Self(TagFmt::SEQUENCE, content)
    }

    /// An IMPLICIT-tagged `SEQUENCE OF`.
    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64, content: C) -> Self
        returns
            Self(
                Tag { class, constructed: true, number: super::tag::tag_num_from_uint(number) },
                content,
            ),
    {
        Self(
            Tag { class, constructed: true, number: super::tag::tag_num_from_uint(number) },
            content,
        )
    }
}

mod sequence_of_specs {
    use super::*;

    impl<C: SpecCombinator> SpecParser for BerSequenceOfFmt<C> {
        type PVal = Seq<C::T>;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ber_sequence_of_fmt(self.0, self.1).spec_parse(ibuf)
        }
    }

    impl<C: SpecCombinator> Consistency for BerSequenceOfFmt<C> {
        type Val = Seq<C::T>;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            ber_sequence_of_fmt(self.0, self.1).consistent(value)
        }
    }

    impl<C: SpecCombinator> SpecSerializerDps for BerSequenceOfFmt<C> {
        type SValue = Seq<C::T>;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ber_sequence_of_fmt(self.0, self.1).spec_serialize_dps(value, obuf)
        }
    }

    impl<C: SpecCombinator> SpecSerializer for BerSequenceOfFmt<C> {
        type SVal = Seq<C::T>;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_sequence_of_fmt(self.0, self.1).spec_serialize(value)
        }
    }

    impl<C: SpecCombinator> SpecByteLen for BerSequenceOfFmt<C> {
        type T = Seq<C::T>;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            ber_sequence_of_fmt(self.0, self.1).byte_len(value)
        }
    }

}

mod sequence_of_proofs {
    use super::*;

    impl<C: SpecCombinator + SafeParser> SafeParser for BerSequenceOfFmt<C> {
        open spec fn safe_inv(&self) -> bool {
            self.1.safe_inv()
        }

        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            ber_sequence_of_fmt(self.0, self.1).lemma_parse_safe(ibuf);
        }
    }

    impl<C: SpecCombinator + SafeParser> Productive for BerSequenceOfFmt<C> {
        open spec fn productive_inv(&self) -> bool {
            self.1.safe_inv()
        }

        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            ber_sequence_of_fmt(self.0, self.1).lemma_productive(ibuf);
        }
    }

    impl<C: SpecCombinator + GoodSerializer> GoodSerializer for BerSequenceOfFmt<C> {
        open spec fn serialize_inv(&self) -> bool {
            self.1.serialize_inv()
        }

        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            ber_sequence_of_fmt(self.0, self.1).lemma_serialize_len(value);
        }
    }

    impl<
        C: SpecCombinator + GoodSerializer + EquivSerializersGeneral,
    > NonTailFmt for BerSequenceOfFmt<C> {
        open spec fn serialize_dps_inv(&self) -> bool {
            &&& self.1.serialize_inv()
            &&& self.1.equiv_general_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_sequence_of_normalized_fmt(self.0, self.1).lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_sequence_of_normalized_fmt(self.0, self.1).lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<C: SpecCombinator + EquivSerializersGeneral> EquivSerializersGeneral for BerSequenceOfFmt<
        C,
    > {
        open spec fn equiv_general_inv(&self) -> bool {
            self.1.equiv_general_inv()
        }

        proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
            ber_sequence_of_normalized_fmt(self.0, self.1).lemma_serialize_equiv(value, obuf);
        }
    }

    impl<C: SpecCombinator + EquivSerializersGeneral> EquivSerializers for BerSequenceOfFmt<C> {
        open spec fn equiv_inv(&self) -> bool {
            self.1.equiv_general_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<C> SPRoundTripDps for BerSequenceOfFmt<C> where
        C:
            SpecCombinator + Productive + GoodSerializer + NonTailFmt + SPRoundTripDps + EquivSerializersGeneral,
     {
        open spec fn unambiguous(&self) -> bool {
            &&& RepeatTillEnd(self.1).sp_roundtrip_inv()
            &&& disjoint_domains(self.1, EOC)
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            ber_sequence_of_fmt(self.0, self.1).theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

}

#[cfg(feature = "alloc")]
impl<'i, C> Parser<&'i [u8]> for BerSequenceOfFmt<C> where
    C: SpecCombinator + Parser<&'i [u8]> + Productive + Copy,
 {
    type PT = Vec<C::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
        &&& self.1.productive_inv()
    }

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use super::tag::lemma_const_tag_fmt_exec_inv;

        let _ = ibuf.len();
        let (tag_len, _tag) = Const(TagFmt, self.0).parse(ibuf)?;
        let after_tag = ibuf.skip(tag_len);
        let (length_len, length) = BerLengthFmt.parse(&after_tag)?;
        let content = after_tag.skip(length_len);

        let (content_len, values) = match length {
            BerLength::Definite(len) => {
                let exact = ExactLen(len, RepeatTillEnd(self.1));
                exact.parse(&content)?
            },
            BerLength::Indefinite => {
                let repeated = Repeat(self.1, EOC);
                let (n, (values, _eoc)) = repeated.parse(&content)?;
                (n, values)
            },
        };
        let total = tag_len + length_len + content_len;
        assert(self.spec_parse(ibuf@) == Some((total as int, values.deep_view())));
        Ok((total, values))
    }
}

impl<Output: OutputBuf, C, T> Serializer<Output, &[T]> for BerSequenceOfFmt<C> where
    C: SpecCombinator + Serializer<Output, T> + ByteLen<T> + Copy,
    T: DeepView,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& <C as Serializer<Output, T>>::exec_inv(&self.1)
        &&& <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn serialize_into(&self, value: &&[T], obuf: &mut Output) {
        let normalized = ASN1Fmt::<_, BER>(self.0, RepeatTillEnd(self.1));
        normalized.serialize_into(value, obuf);
    }
}

impl<C, T> Prepare<&[T]> for BerSequenceOfFmt<C> where
    C: SpecCombinator + Prepare<T> + Copy,
    T: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as Prepare<T>>::exec_inv(&self.1)
    }

    fn prepare(&self, value: &&[T]) -> Result<usize, PreSerializeError> {
        let normalized = ASN1Fmt::<_, BER>(self.0, RepeatTillEnd(self.1));
        normalized.prepare(value)
    }
}

impl<C, T> ByteLen<&[T]> for BerSequenceOfFmt<C> where
    C: SpecCombinator + ByteLen<T> + Copy,
    T: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn length(&self, value: &&[T]) -> usize {
        let normalized = ASN1Fmt::<_, BER>(self.0, RepeatTillEnd(self.1));
        normalized.length(value)
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf, C, T> Serializer<Output, Vec<T>> for BerSequenceOfFmt<C> where
    C: SpecCombinator + Serializer<Output, T> + ByteLen<T> + Copy,
    T: DeepView,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& <C as Serializer<Output, T>>::exec_inv(&self.1)
        &&& <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn serialize_into(&self, value: &Vec<T>, obuf: &mut Output) {
        let normalized = ASN1Fmt::<_, BER>(self.0, RepeatTillEnd(self.1));
        normalized.serialize_into(value, obuf);
    }
}

#[cfg(feature = "alloc")]
impl<C, T> Prepare<Vec<T>> for BerSequenceOfFmt<C> where
    C: SpecCombinator + Prepare<T> + Copy,
    T: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as Prepare<T>>::exec_inv(&self.1)
    }

    fn prepare(&self, value: &Vec<T>) -> Result<usize, PreSerializeError> {
        let normalized = ASN1Fmt::<_, BER>(self.0, RepeatTillEnd(self.1));
        normalized.prepare(value)
    }
}

#[cfg(feature = "alloc")]
impl<C, T> ByteLen<Vec<T>> for BerSequenceOfFmt<C> where
    C: SpecCombinator + ByteLen<T> + Copy,
    T: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn length(&self, value: &Vec<T>) -> usize {
        let normalized = ASN1Fmt::<_, BER>(self.0, RepeatTillEnd(self.1));
        normalized.length(value)
    }
}

/// Return the primitive form of a tag identity.
#[verifier::allow_in_spec]
pub fn primitive_tag(tag: Tag) -> Tag
    returns
        (Tag { class: tag.class, constructed: false, number: tag.number }),
{
    Tag { class: tag.class, constructed: false, number: tag.number }
}

/// Return the constructed form of a tag identity.
#[verifier::allow_in_spec]
pub fn constructed_tag(tag: Tag) -> Tag
    returns
        (Tag { class: tag.class, constructed: true, number: tag.number }),
{
    Tag { class: tag.class, constructed: true, number: tag.number }
}

type BerOctetStringWireType = (
    Tag,
    Sum<(usize, Seq<u8>), Sum<(BerLength, Sum<Seq<Seq<u8>>, (Seq<Seq<u8>>, (u8, u8))>), Never>>,
);

type BerOctetStringBodyFmt<Rec> = Mapped<
    Bind<
        TagFmt,
        spec_fn(Tag) -> Sum<
            Bind<LengthFmt<BER>, spec_fn(usize) -> ExactLen<OctetStringFmt, usize>>,
            Sum<
                Bind<
                    BerLengthFmt,
                    spec_fn(BerLength) -> Sum<
                        ExactLen<RepeatTillEnd<Rec>, usize>,
                        Repeat<Rec, EocFmt>,
                    >,
                >,
                Void,
            >,
        >,
    >,
    FnSpecMapper<BerOctetStringWireType, Seq<u8>>,
>;

/// One full TLV unfolding of a BER OCTET STRING.
///
/// X.690, 8.23.3 specifies a restricted character string as
/// `[UNIVERSAL x] IMPLICIT OCTET STRING`. Thus `tag` applies only to the outermost TLV; constructed
/// fragments recursively use universal OCTET STRING tag 4, as required by X.690, 8.7.3.2.
pub open spec fn ber_octet_string_rec_body(
    tag: Tag,
    rec: ParamRecSpecs<Tag, Seq<u8>>,
) -> BerOctetStringBodyFmt<BundledSpecs<Seq<u8>>> {
    #[verusfmt::skip]
    Mapped {
        inner: Bind(TagFmt, |parsed_tag: Tag|
            match parsed_tag {
                t if t == primitive_tag(tag) =>
                    L(Bind(LengthFmt::<BER>, |len: usize| ExactLen(len, OctetStringFmt))),
                t if t == constructed_tag(tag) =>
                    R(L(Bind(BerLengthFmt, |len: BerLength|
                        match len {
                            BerLength::Definite(len) =>
                                L(ExactLen(len, RepeatTillEnd(rec(TagFmt::OCTET_STRING)))),
                            BerLength::Indefinite =>
                                R(Repeat(rec(TagFmt::OCTET_STRING), EOC)),
                        }))),
                _ => R(R(Void("Tag must match the configured BER OCTET STRING identity"))),
            },
        ),
        mapper: (
            |parsed: BerOctetStringWireType|
                match parsed.1 {
                    L((_len, bytes)) => bytes,
                    R(L((_len, inner))) => match inner {
                        L(segments) => segments.flatten(),
                        R((segments, _eoc)) => segments.flatten(),
                    },
                    R(R(_)) => arbitrary(), // unreachable
                },
            |bytes: Seq<u8>| (primitive_tag(tag), L((bytes.len() as usize, bytes))),
        ),
    }
}

pub struct BerOctetStringRecBody;

impl SpecRecBody for BerOctetStringRecBody {
    type Param = Tag;

    type T = Seq<u8>;

    type Body = BerOctetStringBodyFmt<BundledSpecs<Seq<u8>>>;

    open spec fn spec_body(
        &self,
        tag: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        ber_octet_string_rec_body(tag, rec)
    }
}

mod recursive_proofs {
    use super::*;

    impl SafeParserRecBody for BerOctetStringRecBody {
        proof fn lemma_body_safe_inv_preservation(
            &self,
            tag: Tag,
            rec: ParamRecSpecs<Tag, Seq<u8>>,
        ) {
        }
    }

    impl ProductiveRecBody for BerOctetStringRecBody {
        proof fn lemma_body_productive_inv_preservation(
            &self,
            tag: Tag,
            rec: ParamRecSpecs<Tag, Seq<u8>>,
        ) {
        }
    }

}

/// The primitive, definite-length encoding selected by the reverse mapper.
pub open spec fn ber_octet_string_normalized_fmt(tag: Tag) -> ASN1Fmt<OctetStringFmt, BER> {
    ASN1Fmt(primitive_tag(tag), OctetStringFmt)
}

/// BER OCTET STRING with bounded recursive nesting and a configurable outer tag identity.
///
/// Use [`Self::universal`] for an ordinary OCTET STRING or [`Self::implicit`] for an
/// IMPLICIT-tagged value. The stored tag's constructed bit is normalized away: parsing accepts
/// either primitive or constructed form and serialization always emits primitive definite form.
#[derive(Clone, Copy)]
pub struct BerOctetStringFmt<const LIMIT: usize>(pub Tag);

impl<const LIMIT: usize> BerOctetStringFmt<LIMIT> {
    /// Ordinary universal OCTET STRING.
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::OCTET_STRING),
    {
        Self(TagFmt::OCTET_STRING)
    }

    /// An IMPLICIT-tagged OCTET STRING. Only the outermost tag identity is replaced.
    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self(Tag { class, constructed: false, number: super::tag::tag_num_from_uint(number) }),
    {
        Self(Tag { class, constructed: false, number: super::tag::tag_num_from_uint(number) })
    }
}

mod derived_specs {
    use super::*;

    impl<const LIMIT: usize> SpecParser for BerOctetStringFmt<LIMIT> {
        type PVal = Seq<u8>;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for BerOctetStringFmt<LIMIT> {
        type Val = Seq<u8>;

        open(super) spec fn consistent(&self, value: Self::Val) -> bool {
            ber_octet_string_normalized_fmt(self.0).consistent(value)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for BerOctetStringFmt<LIMIT> {
        type SValue = Seq<u8>;

        open(super) spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<
            u8,
        > {
            ber_octet_string_normalized_fmt(self.0).spec_serialize_dps(value, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for BerOctetStringFmt<LIMIT> {
        type SVal = Seq<u8>;

        open(super) spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_octet_string_normalized_fmt(self.0).spec_serialize(value)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for BerOctetStringFmt<LIMIT> {
        type T = Seq<u8>;

        open(super) spec fn byte_len(&self, value: Self::T) -> nat {
            ber_octet_string_normalized_fmt(self.0).byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const LIMIT: usize> SafeParser for BerOctetStringFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> Productive for BerOctetStringFmt<LIMIT> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).lemma_productive(ibuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, value: Seq<u8>) {
            ber_octet_string_normalized_fmt(self.0).lemma_serialize_len(value);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.lemma_serialize_equiv(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Seq<u8>) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for BerOctetStringFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

}

impl<const LIMIT: usize, Output: OutputBuf> Serializer<Output, [u8]> for BerOctetStringFmt<LIMIT> {
    fn serialize_into(&self, value: &[u8], obuf: &mut Output) {
        let tag = Tag { class: self.0.class, constructed: false, number: self.0.number };
        let normalized = ASN1Fmt::<OctetStringFmt, BER>(tag, OctetStringFmt);
        normalized.serialize_into(value, obuf);
    }
}

impl<const LIMIT: usize> Prepare<[u8]> for BerOctetStringFmt<LIMIT> {
    fn prepare(&self, value: &[u8]) -> Result<usize, PreSerializeError> {
        let tag = Tag { class: self.0.class, constructed: false, number: self.0.number };
        let normalized = ASN1Fmt::<OctetStringFmt, BER>(tag, OctetStringFmt);
        normalized.prepare(value)
    }
}

impl<const LIMIT: usize> ByteLen<[u8]> for BerOctetStringFmt<LIMIT> {
    fn length(&self, value: &[u8]) -> usize {
        let tag = Tag { class: self.0.class, constructed: false, number: self.0.number };
        let normalized = ASN1Fmt::<OctetStringFmt, BER>(tag, OctetStringFmt);
        normalized.length(value)
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize, Output: OutputBuf> Serializer<Output, Vec<u8>> for BerOctetStringFmt<
    LIMIT,
> {
    fn serialize_into(&self, value: &Vec<u8>, obuf: &mut Output) {
        self.serialize_into(value.as_slice(), obuf)
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize> Prepare<Vec<u8>> for BerOctetStringFmt<LIMIT> {
    fn prepare(&self, value: &Vec<u8>) -> Result<usize, PreSerializeError> {
        self.prepare(value.as_slice())
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize> ByteLen<Vec<u8>> for BerOctetStringFmt<LIMIT> {
    fn length(&self, value: &Vec<u8>) -> usize {
        self.length(value.as_slice())
    }
}

#[cfg(feature = "alloc")]
fn flatten_octet_segments(segments: Vec<Vec<u8>>) -> (flat: Vec<u8>)
    ensures
        flat@ == segments.deep_view().flatten(),
{
    broadcast use vstd::seq_lib::group_seq_properties;

    let mut flat = Vec::new();
    let ghost segment_views = segments.deep_view();
    for i in 0..segments.len()
        invariant
            segments.deep_view() == segment_views,
            flat@ == segment_views.take(i as int).flatten(),
    {
        let segment = &segments[i];
        proof {
            let prefix = segment_views.take(i as int);
            prefix.lemma_flatten_push(segment@);
            assert(segment_views[i as int] == segment@);
            assert(segment_views.take(i as int + 1) == prefix.push(segment@));
        }
        flat.extend_from_slice(&segment);
    }
    flat
}

spec fn flattened_result(r: Option<(int, Seq<Seq<u8>>)>) -> Option<(int, Seq<u8>)> {
    match r {
        Some((n, segments)) => Some((n, segments.flatten())),
        None => None,
    }
}

spec fn flattened_result_eoc(r: Option<(int, (Seq<Seq<u8>>, (u8, u8)))>) -> Option<(int, Seq<u8>)> {
    match r {
        Some((n, (segments, _eoc))) => Some((n, segments.flatten())),
        None => None,
    }
}

#[inline(always)]
#[cfg(feature = "alloc")]
fn parse_segments_flatten<I, P>(parser: &P, ibuf: &I) -> (r: PResult<Vec<u8>>) where
    I: InputBuf,
    P: Parser<I, PT = Vec<Vec<u8>>, PVal = Seq<Seq<u8>>>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(r, flattened_result(parser.spec_parse(ibuf@))),
{
    let (n, segments) = parser.parse(ibuf)?;
    let flat = flatten_octet_segments(segments);
    assert(flat.deep_view() == flat@);
    Ok((n, flat))
}

#[inline(always)]
#[cfg(feature = "alloc")]
fn parse_segments_eoc_flatten<I, P>(parser: &P, ibuf: &I) -> (r: PResult<Vec<u8>>) where
    I: InputBuf,
    P: Parser<I, PT = (Vec<Vec<u8>>, (u8, u8)), PVal = (Seq<Seq<u8>>, (u8, u8))>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(r, flattened_result_eoc(parser.spec_parse(ibuf@))),
{
    let (n, (segments, _eoc)) = parser.parse(ibuf)?;
    let flat = flatten_octet_segments(segments);
    assert(flat.deep_view() == flat@);
    Ok((n, flat))
}

#[cfg(feature = "alloc")]
impl<'i> ParserRecBody<&'i [u8]> for BerOctetStringRecBody {
    type EP = Tag;

    type O = Vec<u8>;

    fn parse_body<Exec>(
        &self,
        expected: &Tag,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Tag, Seq<u8>>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Vec<u8>> where Exec: Fn(&Tag, &&'i [u8]) -> PResult<Vec<u8>> {
        use crate::core::exec::bridge_lemmas::*;
        use crate::combinators::congruence::*;

        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use lemma_parser_congruent_reflexive;

        let _ = ibuf.len();
        let (tag_len, actual_tag) = TagFmt.parse(ibuf)?;
        let rest = ibuf.skip(tag_len);

        if actual_tag == primitive_tag(*expected) {
            let (length_len, content_len) = LengthFmt::<BER>.parse(&rest)?;
            let content_bytes = rest.skip(length_len);
            let (content_len, v) = ExactLen(content_len, OctetStringFmt).parse(&content_bytes)?;
            let v = slice_to_vec(v);
            assert(v.deep_view() == v@);
            let total = tag_len + length_len + content_len;
            Ok((total, v))
        } else if actual_tag == constructed_tag(*expected) {
            let (length_len, content_len) = BerLengthFmt.parse(&rest)?;
            let content_bytes = rest.skip(length_len);
            let ghost child_spec = spec_rec(TagFmt::OCTET_STRING);
            let child_exec = |input: &&'i [u8]| -> (r: PResult<Vec<u8>>)
                ensures
                    parse_matches_spec(r, child_spec.2(input@)),
                { exec_rec(&TagFmt::OCTET_STRING, input) };
            // The explicit spec type is required by ordinary rustc: the value of a
            // `Ghost<_>` is erased, so it cannot by itself drive type inference outside Verus.
            let child: &FnParser<&'i [u8], Vec<u8>, BundledSpecs<Seq<u8>>, _> = &FnParser::new(
                child_exec,
                Ghost(child_spec),
            );
            proof {
                lemma_ref_parser_exec_inv::<&'i [u8], _>(child);
                lemma_ref_safe_productive_inv(child);
                lemma_ref_fn_parser_congruence(child);
            }

            let (content_len, v) = match content_len {
                BerLength::Definite(content_len) => {
                    let ghost repeated_spec = RepeatTillEnd(child_spec);
                    let repeated = RepeatTillEnd(child);
                    let exact = ExactLen(content_len, repeated);
                    proof {
                        lemma_repeat_till_end_parser_exec_inv::<&'i [u8], _>(&repeated);
                        lemma_exact_len_parser_exec_inv::<&'i [u8], _, _>(&exact);
                        lemma_repeat_till_end_parser_congruence(child, child_spec);
                        lemma_exact_len_parser_congruence(content_len, repeated, repeated_spec);
                        reveal(parser_congruent);
                    }
                    parse_segments_flatten(&exact, &content_bytes)?
                },
                BerLength::Indefinite => {
                    let repeated = Repeat(child, EOC);
                    proof {
                        lemma_repeat_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                        lemma_repeat_parser_congruence(child, child_spec, EOC, EOC);
                        reveal(parser_congruent);
                    }
                    parse_segments_eoc_flatten(&repeated, &content_bytes)?
                },
            };
            let total = tag_len + length_len + content_len;
            Ok((total, v))
        } else {
            Err(ParseError::custom("Tag must match the configured BER OCTET STRING identity"))
        }
    }
}

#[cfg(feature = "alloc")]
impl<'i, const LIMIT: usize> Parser<&'i [u8]> for BerOctetStringFmt<LIMIT> {
    type PT = Vec<u8>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).parse(ibuf)
    }
}

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

mod restricted_string_specs {
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

mod restricted_string_proofs {
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
                Tag { class, constructed: false, number: super::tag::tag_num_from_uint(number) },
                content,
            ),
    {
        Self(
            Tag { class, constructed: false, number: super::tag::tag_num_from_uint(number) },
            content,
        )
    }
}

pub type BerUtf8StringFmt<const LIMIT: usize> = BerCharStringFmt<Utf8StringFmt, LIMIT>;

pub type BerPrintableStringFmt<const LIMIT: usize> = BerCharStringFmt<PrintableStringFmt, LIMIT>;

pub type BerIa5StringFmt<const LIMIT: usize> = BerCharStringFmt<Ia5StringFmt, LIMIT>;

pub type BerTeletexStringFmt<const LIMIT: usize> = BerCharStringFmt<TeletexStringFmt, LIMIT>;

pub type BerBmpStringFmt<const LIMIT: usize> = BerCharStringFmt<BmpStringFmt, LIMIT>;

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
        if super::utf8string::is_valid_utf8(input) {
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
        if !super::printablestring::is_valid_printable_string(input) {
            Err(ParseError::custom("Invalid PrintableString"))
        } else if !super::utf8string::is_valid_utf8(input) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            // SAFETY: the preceding check establishes that `bytes` is valid UTF-8.
            let inner = unsafe { String::from_utf8_unchecked(bytes) };
            Ok(PrintableStringOwned::new(inner))
        }
    }
}

#[cfg(feature = "alloc")]
impl BerDecoderOwned for Ia5StringFmt {
    type Owned = Ia5StringOwned;

    fn decode_owned(&self, bytes: Vec<u8>) -> Result<Self::Owned, ParseError> {
        broadcast use vstd::utf8::decode_utf8_encode_utf8;

        let input = bytes.as_slice();
        if !super::ia5string::is_valid_ia5_string(input) {
            Err(ParseError::custom("Invalid IA5String"))
        } else if !super::utf8string::is_valid_utf8(input) {
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
        if !super::teletexstring::is_valid_teletex_string(input) {
            Err(ParseError::custom("Invalid TeletexString"))
        } else if !super::utf8string::is_valid_utf8(input) {
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

/// Control the maximum recursion depth for BER OCTET STRING and restricted character string parsing.
pub const MAX_RECURSION_DEPTH: usize = 30;

/// Uniform notation aliases used by schema generators.
pub type BoolTlvFmt = ASN1Fmt<BoolFmt<BER>, BER>;

pub type AnyTlvFmt = AnyFmt<BER>;

pub type IntegerTlvFmt = ASN1Fmt<IntegerFmt, BER>;

pub type Integer8TlvFmt = ASN1Fmt<Integer8Fmt, BER>;

pub type Integer16TlvFmt = ASN1Fmt<Integer16Fmt, BER>;

pub type EnumeratedTlvFmt = ASN1Fmt<EnumeratedFmt, BER>;

pub type ObjectIdentifierTlvFmt = ASN1Fmt<ObjectIdentifierFmt, BER>;

pub type RealTlvFmt = ASN1Fmt<RealFmt, BER>;

pub type BitStringTlvFmt = BerBitStringFmt<MAX_RECURSION_DEPTH>;

pub type OctetStringTlvFmt = BerOctetStringFmt<MAX_RECURSION_DEPTH>;

pub type NullTlvFmt = ASN1Fmt<NullFmt, BER>;

pub type Utf8StringTlvFmt = BerUtf8StringFmt<MAX_RECURSION_DEPTH>;

pub type PrintableStringTlvFmt = BerPrintableStringFmt<MAX_RECURSION_DEPTH>;

pub type TeletexStringTlvFmt = BerTeletexStringFmt<MAX_RECURSION_DEPTH>;

pub type Ia5StringTlvFmt = BerIa5StringFmt<MAX_RECURSION_DEPTH>;

pub type UtcTimeTlvFmt = ASN1Fmt<UtcTimeFmt<BER>, BER>;

pub type GeneralizedTimeTlvFmt = ASN1Fmt<GeneralizedTimeFmt<BER>, BER>;

pub type BmpStringTlvFmt = BerBmpStringFmt<MAX_RECURSION_DEPTH>;

pub type SequenceFmt<C> = BerSequenceFmt<C>;

pub type SequenceOfFmt<C> = BerSequenceOfFmt<C>;

pub type SetOfTlvFmt<C> = BerSequenceOfFmt<C>;

pub type ExplicitFmt<C> = BerSequenceFmt<C>;

pub type DefaultFmt<Field, Default, Rest> = super::DefaultedFmt<Field, Default, Rest, BER>;

pub const BOOLEAN: BoolTlvFmt = ASN1Fmt(TagFmt::BOOLEAN, BoolFmt::<BER>);

pub const ANY: AnyTlvFmt = AnyFmt::<BER>;

pub const INTEGER: IntegerTlvFmt = ASN1Fmt(TagFmt::INTEGER, IntegerFmt);

pub const INTEGER8: Integer8TlvFmt = ASN1Fmt(TagFmt::INTEGER, Integer8Fmt);

pub const INTEGER16: Integer16TlvFmt = ASN1Fmt(TagFmt::INTEGER, Integer16Fmt);

pub const ENUMERATED: EnumeratedTlvFmt = ASN1Fmt(TagFmt::ENUMERATED, EnumeratedFmt);

pub const OBJECT_IDENTIFIER: ObjectIdentifierTlvFmt = ASN1Fmt(
    TagFmt::OBJECT_IDENTIFIER,
    ObjectIdentifierFmt,
);

pub const REAL: RealTlvFmt = ASN1Fmt(TagFmt::REAL, RealFmt);

pub const BIT_STRING: BitStringTlvFmt = BerBitStringFmt(TagFmt::BIT_STRING);

pub const NULL: NullTlvFmt = ASN1Fmt(TagFmt::NULL, NullFmt);

pub const UTC_TIME: UtcTimeTlvFmt = ASN1Fmt(TagFmt::UTC_TIME, UtcTimeFmt::<BER>);

pub const GENERALIZED_TIME: GeneralizedTimeTlvFmt = ASN1Fmt(
    TagFmt::GENERALIZED_TIME,
    GeneralizedTimeFmt::<BER>,
);

pub const OCTET_STRING: OctetStringTlvFmt = BerOctetStringFmt(TagFmt::OCTET_STRING);

pub const UTF8_STRING: Utf8StringTlvFmt = BerCharStringFmt(TagFmt::UTF8_STRING, Utf8StringFmt);

pub const PRINTABLE_STRING: PrintableStringTlvFmt = BerCharStringFmt(
    TagFmt::PRINTABLE_STRING,
    PrintableStringFmt,
);

pub const IA5_STRING: Ia5StringTlvFmt = BerCharStringFmt(TagFmt::IA5_STRING, Ia5StringFmt);

pub const TELETEX_STRING: TeletexStringTlvFmt = BerCharStringFmt(
    TagFmt::TELETEX_STRING,
    TeletexStringFmt,
);

pub const BMP_STRING: BmpStringTlvFmt = BerCharStringFmt(TagFmt::BMP_STRING, BmpStringFmt);

/// Construct a BER `SEQUENCE`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SEQUENCE<C: Copy>(content: C) -> SequenceFmt<C>
    returns
        BerSequenceFmt(TagFmt::SEQUENCE, content),
{
    BerSequenceFmt::universal(content)
}

/// Construct a BER `SEQUENCE OF`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SEQUENCE_OF<C: Copy>(content: C) -> SequenceOfFmt<C>
    returns
        BerSequenceOfFmt(TagFmt::SEQUENCE, content),
{
    BerSequenceOfFmt::universal(content)
}

/// Construct a BER `SET OF`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SET_OF<C: Copy>(content: C) -> SetOfTlvFmt<C>
    returns
        BerSequenceOfFmt(TagFmt::SET, content),
{
    BerSequenceOfFmt(TagFmt::SET, content)
}

/// Apply an ASN.1 EXPLICIT tag with an arbitrary tag class.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn Explicit<C: Copy>(class: Class, number: u64, inner: C) -> ExplicitFmt<C>
    returns
        BerSequenceFmt(explicit_tag(class, number), inner),
{
    BerSequenceFmt(explicit_tag(class, number), inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::ContextSpecific, number, inner),
{
    Explicit(Class::ContextSpecific, number, inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT_APPLICATION<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::Application, number, inner),
{
    Explicit(Class::Application, number, inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT_PRIVATE<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::Private, number, inner),
{
    Explicit(Class::Private, number, inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn DEFAULT<Field, Rest>(field: Field, default: Field::T, cont: Rest) -> DefaultFmt<
    Field,
    Field::T,
    Rest,
> where Field: SpecByteLen
    returns
        defaulted::<Field, Rest, BER>(field, default, cont),
{
    defaulted::<Field, Rest, BER>(field, default, cont)
}

} // verus!
#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use crate::asn1::{BmpString, Integer8Fmt};
    use crate::core::exec::{ParseErrorKind, Parser, Prepare, SerializerExt};

    type Octets = BerOctetStringFmt<8>;

    fn parse_universal(input: &[u8]) -> (usize, Vec<u8>) {
        Octets::universal().parse(&input).unwrap()
    }

    fn integer_sequence() -> BerSequenceOfFmt<ASN1Fmt<Integer8Fmt, BER>> {
        SEQUENCE_OF(ASN1Fmt(TagFmt::INTEGER, Integer8Fmt))
    }

    fn integer_fields_sequence(
    ) -> BerSequenceFmt<Pair<ASN1Fmt<Integer8Fmt, BER>, ASN1Fmt<Integer8Fmt, BER>>> {
        let integer = ASN1Fmt::<_, BER>(TagFmt::INTEGER, Integer8Fmt);
        SEQUENCE(Pair(integer, integer))
    }

    #[test]
    fn ber_sequence_parses_definite_and_indefinite_schema_bodies() {
        let format = integer_fields_sequence();
        let definite = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        let indefinite = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];

        assert_eq!(
            format.parse(&&definite[..]).unwrap(),
            (definite.len(), (1i8, 2i8)),
        );
        assert_eq!(
            format.parse(&&indefinite[..]).unwrap(),
            (indefinite.len(), (1i8, 2i8)),
        );

        let missing_eoc = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        assert!(format.parse(&&missing_eoc[..]).is_err());

        let extra_component = [
            0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x02, 0x01, 0x03, 0x00, 0x00,
        ];
        assert!(format.parse(&&extra_component[..]).is_err());
    }

    #[test]
    fn ber_sequence_supports_implicit_tags_and_definite_normalization() {
        let content = integer_fields_sequence().1;
        let format = BerSequenceFmt::implicit(Class::ContextSpecific, 0, content);
        let indefinite = [0xa0, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];
        let (_, value) = format.parse(&&indefinite[..]).unwrap();
        assert_eq!(value, (1i8, 2i8));

        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0xa0, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02]);

        let universal = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        assert!(format.parse(&&universal[..]).is_err());
    }

    #[test]
    fn ber_sequence_of_parses_definite_and_indefinite_forms() {
        let format = integer_sequence();
        let definite = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        let indefinite = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];

        assert_eq!(
            format.parse(&&definite[..]).unwrap(),
            (definite.len(), vec![1i8, 2i8]),
        );
        assert_eq!(
            format.parse(&&indefinite[..]).unwrap(),
            (indefinite.len(), vec![1i8, 2i8]),
        );

        let empty_definite = [0x30, 0x00];
        let empty_indefinite = [0x30, 0x80, 0x00, 0x00];
        assert_eq!(
            format.parse(&&empty_definite[..]).unwrap(),
            (empty_definite.len(), Vec::<i8>::new()),
        );
        assert_eq!(
            format.parse(&&empty_indefinite[..]).unwrap(),
            (empty_indefinite.len(), Vec::<i8>::new()),
        );
    }

    #[test]
    fn ber_sequence_of_supports_implicit_outer_tags() {
        let element = ASN1Fmt::<_, BER>(TagFmt::INTEGER, Integer8Fmt);
        let format = BerSequenceOfFmt::implicit(Class::ContextSpecific, 0, element);
        let definite = [0xa0, 0x03, 0x02, 0x01, 0x01];
        let indefinite = [0xa0, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00];

        assert_eq!(
            format.parse(&&definite[..]).unwrap(),
            (definite.len(), vec![1i8]),
        );
        assert_eq!(
            format.parse(&&indefinite[..]).unwrap(),
            (indefinite.len(), vec![1i8]),
        );

        let universal = [0x30, 0x03, 0x02, 0x01, 0x01];
        assert!(format.parse(&&universal[..]).is_err());

        let value = vec![1i8];
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, definite);
    }

    #[test]
    fn ber_sequence_of_serialization_normalizes_to_definite_form() {
        let format = integer_sequence();
        let indefinite = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];
        let (_, value) = format.parse(&&indefinite[..]).unwrap();
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());

        assert_eq!(output, [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02]);
    }

    #[test]
    fn nested_ber_sequence_of_delegates_indefinite_values_to_the_element_codec() {
        let inner = integer_sequence();
        let outer = SEQUENCE_OF(inner);
        let input = [
            0x30, 0x80, // outer indefinite SEQUENCE OF
            0x30, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00, // inner indefinite value
            0x30, 0x03, 0x02, 0x01, 0x02, // inner definite value
            0x00, 0x00, // outer EOC
        ];

        assert_eq!(
            outer.parse(&&input[..]).unwrap(),
            (input.len(), vec![vec![1i8], vec![2i8]]),
        );
    }

    #[test]
    fn ber_sequence_of_rejects_missing_eoc_and_non_elements() {
        let format = integer_sequence();
        let missing_eoc = [0x30, 0x80, 0x02, 0x01, 0x01];
        assert!(format.parse(&&missing_eoc[..]).is_err());

        let boolean_element = [0x30, 0x80, 0x01, 0x01, 0xff, 0x00, 0x00];
        assert!(format.parse(&&boolean_element[..]).is_err());
    }

    #[test]
    fn parses_primitive_and_definite_constructed_octet_strings() {
        let primitive = [0x04, 0x03, b'a', b'b', b'c'];
        assert_eq!(
            parse_universal(&primitive),
            (primitive.len(), b"abc".to_vec())
        );

        let constructed = [0x24, 0x07, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c'];
        assert_eq!(
            parse_universal(&constructed),
            (constructed.len(), b"abc".to_vec()),
        );
    }

    #[test]
    fn parses_indefinite_and_nested_constructed_octet_strings() {
        let indefinite = [
            0x24, 0x80, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c', 0x00, 0x00,
        ];
        assert_eq!(
            parse_universal(&indefinite),
            (indefinite.len(), b"abc".to_vec()),
        );

        let nested = [
            0x24, 0x80, 0x24, 0x80, 0x04, 0x01, b'a', 0x00, 0x00, 0x04, 0x01, b'b', 0x00, 0x00,
        ];
        assert_eq!(parse_universal(&nested), (nested.len(), b"ab".to_vec()));
    }

    #[test]
    fn implicit_tagging_replaces_only_the_outer_tag() {
        let format = Octets::implicit(Class::ContextSpecific, 0);

        let primitive = [0x80, 0x03, b'a', b'b', b'c'];
        assert_eq!(
            format.parse(&&primitive[..]).unwrap(),
            (primitive.len(), b"abc".to_vec()),
        );

        let constructed = [
            0xa0, 0x80, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c', 0x00, 0x00,
        ];
        assert_eq!(
            format.parse(&&constructed[..]).unwrap(),
            (constructed.len(), b"abc".to_vec()),
        );

        // Recursive components retain the universal OCTET STRING tag.
        let retagged_child = [0xa0, 0x80, 0x80, 0x01, b'a', 0x00, 0x00];
        assert_eq!(
            format.parse(&&retagged_child[..]).unwrap_err().kind,
            ParseErrorKind::InvalidTag,
        );
    }

    #[test]
    fn rejects_malformed_framing_and_enforces_the_recursion_limit() {
        let missing_eoc = [0x24, 0x80, 0x04, 0x01, b'a'];
        assert!(Octets::universal().parse(&&missing_eoc[..]).is_err());

        let short_definite_body = [0x24, 0x04, 0x04, 0x01, b'a'];
        assert!(Octets::universal()
            .parse(&&short_definite_body[..])
            .is_err());

        let nested_2 = [
            0x24, 0x80, 0x24, 0x80, 0x04, 0x01, b'a', 0x00, 0x00, 0x04, 0x01, b'b', 0x00, 0x00,
        ];
        assert!(BerOctetStringFmt::<1>::universal()
            .parse(&&nested_2[..])
            .is_err());
    }

    #[test]
    fn serialization_normalizes_to_primitive_definite_form() {
        let constructed = [
            0x24, 0x80, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c', 0x00, 0x00,
        ];
        let (_, value) = parse_universal(&constructed);
        let format = Octets::universal();
        let mut output = vec![0; format.prepare(value.as_slice()).unwrap()];
        format.serialize(value.as_slice(), output.as_mut_slice());
        assert_eq!(output, [0x04, 0x03, b'a', b'b', b'c']);

        let implicit = Octets::implicit(Class::ContextSpecific, 0);
        let mut output = vec![0; implicit.prepare(value.as_slice()).unwrap()];
        implicit.serialize(value.as_slice(), output.as_mut_slice());
        assert_eq!(output, [0x80, 0x03, b'a', b'b', b'c']);
    }

    #[test]
    fn ber_utf8_string_validates_after_flattening_segments() {
        type Format = BerUtf8StringFmt<8>;

        // U+20AC is split in the middle of its three-octet UTF-8 encoding. Validating each
        // primitive segment separately would reject this standards-permitted encoding.
        let split_scalar = [
            0x2c, 0x80, 0x04, 0x01, 0xe2, 0x04, 0x02, 0x82, 0xac, 0x00, 0x00,
        ];
        let (n, value) = Format::universal().parse(&&split_scalar[..]).unwrap();
        assert_eq!(n, split_scalar.len());
        assert_eq!(value.as_str(), "€");

        let primitive = [0x0c, 0x03, 0xe2, 0x82, 0xac];
        assert_eq!(
            Format::universal()
                .parse(&&primitive[..])
                .unwrap()
                .1
                .as_str(),
            "€"
        );

        let nested = [
            0x2c, 0x80, // constructed UTF8String
            0x24, 0x80, // nested universal constructed OCTET STRING
            0x04, 0x01, 0xe2, 0x04, 0x02, 0x82, 0xac, 0x00, 0x00, // nested EOC
            0x00, 0x00, // outer EOC
        ];
        assert_eq!(
            Format::universal().parse(&&nested[..]).unwrap().1.as_str(),
            "€"
        );

        let format = Format::universal();
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x0c, 0x03, 0xe2, 0x82, 0xac]);
    }

    #[test]
    fn ber_restricted_strings_support_implicit_outer_tags() {
        type Format = BerUtf8StringFmt<8>;
        let format = Format::implicit(Class::ContextSpecific, 0);
        let input = [
            0xa0, 0x80, 0x04, 0x01, 0xe2, 0x04, 0x02, 0x82, 0xac, 0x00, 0x00,
        ];
        let (_, value) = format.parse(&&input[..]).unwrap();
        assert_eq!(value.as_str(), "€");

        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x80, 0x03, 0xe2, 0x82, 0xac]);
    }

    #[test]
    fn ber_printable_and_ia5_validate_flattened_contents() {
        let printable = [
            0x33, 0x80, 0x04, 0x02, b'A', b'B', 0x04, 0x02, b'1', b'?', 0x00, 0x00,
        ];
        let (_, value) = BerPrintableStringFmt::<8>::universal()
            .parse(&&printable[..])
            .unwrap();
        assert_eq!(value.inner(), "AB1?");

        let invalid_ia5 = [0x36, 0x80, 0x04, 0x01, 0x80, 0x00, 0x00];
        assert!(BerIa5StringFmt::<8>::universal()
            .parse(&&invalid_ia5[..])
            .is_err());
    }

    #[test]
    fn ber_bmp_string_allows_code_units_to_cross_segments() {
        type Format = BerBmpStringFmt<8>;

        // BMPString "A" is 00 41. The code unit is deliberately split between children.
        let split_code_unit = [0x3e, 0x80, 0x04, 0x01, 0x00, 0x04, 0x01, 0x41, 0x00, 0x00];
        let (_, value) = Format::universal().parse(&&split_code_unit[..]).unwrap();
        assert_eq!(value.inner(), "A");

        let malformed = [0x1e, 0x01, 0x00];
        assert!(Format::universal().parse(&&malformed[..]).is_err());
        let surrogate = [0x1e, 0x02, 0xd8, 0x00];
        assert!(Format::universal().parse(&&surrogate[..]).is_err());

        let value = BmpString::new(String::from("A"));
        let format = Format::universal();
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x1e, 0x02, 0x00, 0x41]);
    }
}
