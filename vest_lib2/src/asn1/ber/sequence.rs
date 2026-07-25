//! BER SEQUENCE combinators.
use crate::asn1::{ASN1Fmt, BerLength, BerLengthFmt, Class, Tag, TagFmt, BER};
use crate::combinators::{
    bytes::ExactLen, mapped::spec::FnSpecMapper, Bind, Const, Mapped, Pair, PrefixTagged, Sum,
};
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::*;
use crate::core::exec::{
    ByteLen, OutputBuf, PResult, ParseError, ParseErrorKind, Parser, PreSerializeError, Prepare,
    Serializer,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::any::{EocFmt, EOC};
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

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

mod derived_proofs {
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
        broadcast use crate::asn1::tag::lemma_const_tag_fmt_exec_inv;

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

} // verus!
