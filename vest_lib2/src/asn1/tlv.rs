use crate::asn1::{Length, Tag, TagFmt, ASN1};
use crate::combinators::{
    bytes::ExactLen, length::AsLen, mapped::spec::FnSpecMapper, Bind, Const, Mapped, PrefixTagged,
};
use crate::core::{
    exec::{
        input::{InputBuf, InputSlice},
        parser::{PResult, Parser},
        serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    proof::*,
    spec::*,
};
use vstd::prelude::*;

verus! {

pub type ASN1Fmt__<Content, const DER: bool> = Mapped<
    PrefixTagged<TagFmt, Tag, Bind<Length<DER>, spec_fn(usize) -> ExactLen<Content, usize>>>,
    FnSpecMapper<(usize, <Content as SpecByteLen>::T), <Content as SpecByteLen>::T>,
>;

pub open spec fn asn1_fmt<Content: SpecCombinator, const DER: bool>(
    tag_fmt: Const<TagFmt, Tag>,
    content: Content,
) -> ASN1Fmt__<Content, DER> {
    Mapped {
        inner: PrefixTagged(
            tag_fmt.0,
            tag_fmt.1,
            Bind(Length::<DER>, |len: usize| ExactLen(len, content)),
        ),
        mapper: (|i: (usize, Content::T)| i.1, |o: Content::T| (content.byte_len(o) as usize, o)),
    }
}

mod derived_specs {
    use super::*;

    impl<Content: SpecCombinator, const DER: bool> SpecParser for ASN1<Content, DER> {
        type PVal = Content::PVal;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            asn1_fmt::<Content, DER>(self.0, self.1).spec_parse(ibuf)
        }
    }

    impl<Content: SpecCombinator, const DER: bool> Consistency for ASN1<Content, DER> {
        type Val = Content::PVal;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            asn1_fmt::<Content, DER>(self.0, self.1).consistent(v)
        }
    }

    impl<Content: SpecCombinator, const DER: bool> SpecSerializerDps for ASN1<Content, DER> {
        type SValue = Content::PVal;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            asn1_fmt::<Content, DER>(self.0, self.1).spec_serialize_dps(v, obuf)
        }
    }

    impl<Content: SpecCombinator, const DER: bool> SpecSerializer for ASN1<Content, DER> {
        type SVal = Content::PVal;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            asn1_fmt::<Content, DER>(self.0, self.1).spec_serialize(v)
        }
    }

    impl<Content: SpecCombinator, const DER: bool> SpecByteLen for ASN1<Content, DER> {
        type T = Content::PVal;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            asn1_fmt::<Content, DER>(self.0, self.1).byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<Content: SpecCombinator + SafeParser, const DER: bool> SafeParser for ASN1<Content, DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_parse_safe(ibuf);
        }
    }

    impl<Content: SpecCombinator + Productive, const DER: bool> Productive for ASN1<Content, DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_productive(s);
        }
    }

    impl<Content: SpecCombinator + SoundParser> SoundParser for ASN1<Content, true> {
        open spec fn sound_inv(&self) -> bool {
            &&& self.1.sound_inv()
            &&& self.0.0.consistent(self.0.1)
        }

        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            asn1_fmt::<Content, true>(self.0, self.1).lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            asn1_fmt::<Content, true>(self.0, self.1).lemma_parse_sound_value(ibuf);
        }
    }

    impl<
        Content: SpecCombinator + GoodSerializer + EquivSerializers,
        const DER: bool,
    > NonTailFmt for ASN1<Content, DER> {
        open spec fn serialize_dps_inv(&self) -> bool {
            &&& self.1.serialize_inv()
            &&& self.1.equiv_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, v: Content::PVal, obuf: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Content::PVal, obuf: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<Content: SpecCombinator + GoodSerializer, const DER: bool> GoodSerializer for ASN1<
        Content,
        DER,
    > {
        open spec fn serialize_inv(&self) -> bool {
            self.1.serialize_inv()
        }

        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_serialize_len(v);
        }
    }

    impl<
        Content: SpecCombinator + EquivSerializers + GoodSerializer + SPRoundTrip,
        const DER: bool,
    > SPRoundTripDps for ASN1<Content, DER> {
        open spec fn unambiguous(&self) -> bool {
            &&& self.1.serialize_inv()
            &&& self.1.equiv_inv()
            &&& self.1.sp_roundtrip_inv()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<Content: SpecCombinator + SafeParser, const DER: bool> NoLookAhead for ASN1<Content, DER> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_no_lookahead(i1, i2);
        }
    }

    impl<Content: SpecCombinator + SoundParser + NonMalleable> NonMalleable for ASN1<
        Content,
        true,
    > {
        open spec fn nonmal_inv(&self) -> bool {
            &&& self.1.nonmal_inv()
            &&& self.1.sound_inv()
            &&& self.1.safe_inv()
            &&& self.0.0.consistent(self.0.1)
        }

        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            asn1_fmt::<Content, true>(self.0, self.1).lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<
        Content: SpecCombinator + EquivSerializers,
        const DER: bool,
    > EquivSerializersGeneral for ASN1<Content, DER> {
        open spec fn equiv_general_inv(&self) -> bool {
            self.1.equiv_inv()
        }

        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_serialize_equiv(v, obuf);
        }
    }

    impl<Content: SpecCombinator + EquivSerializers, const DER: bool> EquivSerializers for ASN1<
        Content,
        DER,
    > {
        open spec fn equiv_inv(&self) -> bool {
            self.1.equiv_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            asn1_fmt::<Content, DER>(self.0, self.1).lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i, Content, const DER: bool> Parser<&'i [u8]> for ASN1<Content, DER> where
    Content: SpecCombinator + Parser<&'i [u8]>,
 {
    type PT = Content::PT;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use crate::core::spec::SoundParser::lemma_parse_sound_value;
        broadcast use super::tag::lemma_const_tag_fmt_exec_inv;

        let _ = ibuf.len();

        let (n1, tag_val) = self.0.parse(ibuf)?;
        let rest = ibuf.skip(n1);
        let (n2, len) = Length::<DER>.parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, val) = ExactLen(len, &self.1).parse(&rest)?;
        Ok((n1 + n2 + n3, val))
    }
}

impl<Content, T, const DER: bool> Serializer<T> for ASN1<Content, DER> where
    T: DeepView,
    Content: SpecCombinator + Serializer<T> + ByteLen<T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& <_ as Serializer<T>>::exec_inv(&self.1)
        &&& <_ as ByteLen<T>>::exec_inv(&self.1)
    }

    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        let ghost vv = v.deep_view();
        assert(self.consistent(vv) == (self.1.byte_len(vv) as usize as nat == self.1.byte_len(vv)));
        assert(self.1.byte_len(vv) <= usize::MAX);
        let len = self.1.length(v);
        self.0.serialize(&self.0.1, obuf);
        Length::<DER>.serialize(&len, obuf);
        self.1.serialize(v, obuf);
    }
}

impl<Content, T, const DER: bool> Prepare<T> for ASN1<Content, DER> where
    T: DeepView,
    Content: SpecCombinator + Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn prepare(&self, v: &T) -> Result<usize, PreSerializeError> {
        broadcast use super::tag::lemma_const_tag_fmt_exec_inv;

        let n1 = self.0.prepare(&self.0.1)?;
        let n3 = self.1.prepare(v)?;
        let n2 = Length::<DER>.prepare(&n3)?;
        let total_len = n1.checked_add(n2).ok_or(
            PreSerializeError::length_too_large(),
        )?.checked_add(n3).ok_or(PreSerializeError::length_too_large())?;
        Ok(n1 + n2 + n3)
    }
}

impl<Content, T, const DER: bool> ByteLen<T> for ASN1<Content, DER> where
    T: DeepView,
    Content: SpecCombinator + ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn length(&self, v: &T) -> usize {
        let n1 = self.0.length(&self.0.1);
        let n3 = self.1.length(v);
        let n2 = Length::<DER>.length(&n3);
        n1 + n2 + n3
    }
}

} // verus!
