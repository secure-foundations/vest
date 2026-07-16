//! ASN.1 ANY / open-type values.
//!
//! An ANY value is one complete, self-delimiting TLV. The semantic representation
//! retains the decoded tag and opaque contents bytes.
use crate::combinators::{
    bytes::ExactLen, mapped::spec::FnSpecMapper, Bind, Mapped, Pair, Refined, Tail,
};
use crate::core::exec::input::InputBuf;
use crate::core::exec::output::OutputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::{Any, Length, Tag, TagFmt};

verus! {

pub type AnyWire<const DER: bool> = Pair<
    TagFmt,
    Bind<Length<DER>, spec_fn(usize) -> ExactLen<Tail, usize>>,
>;

pub type AnyFmt<const DER: bool> = Refined<
    Mapped<AnyWire<DER>, FnSpecMapper<(Tag, (usize, Seq<u8>)), AnySpec>>,
    PredFnSpec<AnySpec>,
>;

/// Semantic representation of an open type.
#[verifier::ext_equal]
pub struct AnySpec {
    pub tag: Tag,
    pub content: Seq<u8>,
}

pub open spec fn any_fmt<const DER: bool>() -> AnyFmt<DER> {
    Refined(
        Mapped {
            inner: Pair(TagFmt, Bind(Length::<DER>, |len: usize| ExactLen(len, Tail))),
            mapper: (
                |v: (Tag, (usize, Seq<u8>))| AnySpec { tag: v.0, content: v.1.1 },
                |v: AnySpec| (v.tag, (v.content.len() as usize, v.content)),
            ),
        },
        |v: AnySpec| v.tag != TagFmt::EOC,
    )
}

proof fn lemma_any_mapped_sound_nonmal_inv()
    ensures
        any_fmt::<true>().0.sound_inv(),
        any_fmt::<true>().0.nonmal_inv(),
{
    let mapped = any_fmt::<true>().0;
    assert forall|v: (Tag, (usize, Seq<u8>))| #[trigger] mapped.inner.consistent(v) implies (
    mapped.mapper.1)((mapped.mapper.0)(v)) == v by {
        let (_tag, (len, content)) = v;
        assert(len as nat == content.len());
        assert(content.len() <= usize::MAX);
    }
}

proof fn lemma_any_mapped_unambiguous<const DER: bool>()
    ensures
        any_fmt::<DER>().0.unambiguous(),
{
    let mapped = any_fmt::<DER>().0;
    assert forall|v: AnySpec| #[trigger] mapped.consistent(v) implies (mapped.mapper.0)(
        (mapped.mapper.1)(v),
    ) == v by {}
}

mod derived_specs {
    use super::*;

    impl<const DER: bool> SpecParser for Any<DER> {
        type PVal = AnySpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            any_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for Any<DER> {
        type Val = AnySpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            any_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for Any<DER> {
        type SValue = AnySpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            any_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for Any<DER> {
        type SVal = AnySpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            any_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for Any<DER> {
        type T = AnySpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            any_fmt::<DER>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const DER: bool> SafeParser for Any<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            any_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for Any<DER> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            any_fmt::<DER>().lemma_productive(ibuf);
        }
    }

    impl SoundParser for Any<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_any_mapped_sound_nonmal_inv();
            any_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_any_mapped_sound_nonmal_inv();
            any_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> NonTailFmt for Any<DER> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            any_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            any_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const DER: bool> GoodSerializer for Any<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            any_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for Any<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_any_mapped_unambiguous::<DER>();
            any_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Any<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_any_mapped_sound_nonmal_inv();
            any_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializersGeneral for Any<DER> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            any_fmt::<DER>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const DER: bool> EquivSerializers for Any<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            any_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

/// Borrowed executable open-type value.
pub struct AnyValue<'a> {
    tag: Tag,
    content: &'a [u8],
}

impl<'a> DeepView for AnyValue<'a> {
    type V = AnySpec;

    closed spec fn deep_view(&self) -> Self::V {
        AnySpec { tag: self.tag, content: self.content.deep_view() }
    }
}

impl<'a> AnyValue<'a> {
    pub fn new(tag: Tag, content: &'a [u8]) -> Self {
        Self { tag, content }
    }

    pub fn tag(&self) -> Tag {
        self.tag
    }

    pub fn content(&self) -> &'a [u8] {
        self.content
    }
}

impl<'a, const DER: bool> Parser<&'a [u8]> for Any<DER> {
    type PT = AnyValue<'a>;

    fn parse(&self, ibuf: &&'a [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use crate::core::spec::SoundParser::lemma_parse_sound_value;

        let _ = ibuf.len();
        let (n1, tag) = TagFmt.parse(ibuf)?;
        if tag == TagFmt::EOC {
            return Err(ParseError::invalid_tag());
        }
        let rest = ibuf.skip(n1);
        let (n2, len) = Length::<DER>.parse(&rest)?;
        let rest = rest.skip(n2);
        let (n3, content) = ExactLen(len, Tail).parse(&rest)?;
        Ok((n1 + n2 + n3, AnyValue { tag, content }))
    }
}

impl<'a, Output: OutputBuf, const DER: bool> Serializer<Output, AnyValue<'a>> for Any<DER> {
    fn serialize_into(&self, v: &AnyValue<'a>, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        let len = v.content.len();
        TagFmt.serialize_into(&v.tag, obuf);
        Length::<DER>.serialize_into(&len, obuf);
        Tail.serialize_into(&v.content, obuf);
    }
}

impl<'a, const DER: bool> Prepare<AnyValue<'a>> for Any<DER> {
    fn prepare(&self, v: &AnyValue<'a>) -> Result<usize, PreSerializeError> {
        if v.tag == TagFmt::EOC {
            return Err(PreSerializeError::custom("EOC is not an open-type value"));
        }
        let n1 = TagFmt.prepare(&v.tag)?;
        let content_len = Tail.prepare(&v.content)?;
        let n2 = Length::<DER>.prepare(&content_len)?;
        let header = n1.checked_add(n2).ok_or(PreSerializeError::length_too_large())?;
        let total = header.checked_add(content_len).ok_or(PreSerializeError::length_too_large())?;
        Ok(total)
    }
}

impl<'a, const DER: bool> ByteLen<AnyValue<'a>> for Any<DER> {
    fn length(&self, v: &AnyValue<'a>) -> usize {
        let n1 = TagFmt.length(&v.tag);
        let content_len = Tail.length(&v.content);
        let n2 = Length::<DER>.length(&content_len);
        n1 + n2 + content_len
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use crate::asn1::TagFmt;
    use crate::core::exec::{Parser, Prepare, SerializerExt};

    #[test]
    fn any_roundtrips_one_complete_tlv() {
        let input = [0x30, 0x03, 0x02, 0x01, 0x05, 0xff];
        let (n, value) = super::super::der::ANY.parse(&&input[..]).unwrap();
        assert_eq!(n, 5);
        assert_eq!(value.tag(), TagFmt::SEQUENCE);
        assert_eq!(value.content(), &[0x02, 0x01, 0x05]);

        let mut output = vec![0; super::super::der::ANY.prepare(&value).unwrap()];
        super::super::der::ANY.serialize(&value, &mut output);
        assert_eq!(output, &input[..5]);
    }

    #[test]
    fn any_rejects_eoc_as_a_value() {
        assert!(super::super::der::ANY.parse(&&[0x00, 0x00][..]).is_err());
    }
}
