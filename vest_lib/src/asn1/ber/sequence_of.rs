//! BER SEQUENCE OF / SET OF element list combinators.
use crate::asn1::{ASN1Fmt, BerLength, BerLengthFmt, Class, Tag, TagFmt, BER};
use crate::combinators::{
    bytes::ExactLen, mapped::spec::FnSpecMapper, tail::RepeatTillEnd, Bind, Const, Mapped,
    PrefixTagged, Repeat, Sum,
};
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::*;
use crate::core::exec::{
    ByteLen, OutputBuf, PResult, ParseError, ParseErrorKind, Parser, PreSerializeError, Prepare,
    Serializer,
};
use crate::core::{proof::*, spec::*};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;

use super::any::{parse_discard_eoc, EocFmt, EocValue, EOC};
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

type BerSequenceOfWireType<T> = (BerLength, Sum<Seq<T>, (Seq<T>, EocValue)>);

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
                Tag {
                    class,
                    constructed: true,
                    number: crate::asn1::tag::tag_num_from_uint(number),
                },
                content,
            ),
    {
        Self(
            Tag { class, constructed: true, number: crate::asn1::tag::tag_num_from_uint(number) },
            content,
        )
    }
}

mod derived_specs {
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

mod derived_proofs {
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
        broadcast use crate::asn1::tag::lemma_const_tag_fmt_exec_inv;

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
                proof {
                    crate::core::exec::bridge_lemmas::lemma_pair_parser_exec_inv::<&'i [u8], _, _>(
                        &EOC,
                    );
                    crate::core::exec::bridge_lemmas::lemma_repeat_parser_exec_inv::<
                        &'i [u8],
                        _,
                        _,
                    >(&repeated);
                }
                parse_discard_eoc(&repeated, &content)?
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

} // verus!
