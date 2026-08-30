//! CBOR byte-string and text-string chunk formats (used for indefinite strings).
use alloc::{string::String, vec::Vec};

use crate::asn1::Utf8StringFmt;
use crate::combinators::{
    bytes::ExactLen, mapped::spec::FnSpecMapper, Bind, Mapped, Sum, Tail, Void,
};
use crate::core::exec::{
    input::{InputBuf, InputSlice},
    parser::*,
    ParseError,
};
use crate::core::{proof::*, spec::*};
use crate::Never;
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

use super::{CborHead, CborHeadFmt, CborHeadValue, MajorType};
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

pub type ByteChunkWire = (CborHead, Sum<Seq<u8>, Never>);

pub type ByteChunkInnerFmt<const DET: bool> = Mapped<
    Bind<CborHeadFmt<DET>, spec_fn(CborHead) -> Sum<ExactLen<Tail, u64>, Void>>,
    FnSpecMapper<ByteChunkWire, Seq<u8>>,
>;

/// One definite byte-string chunk. Indefinite strings use this as their repeat element.
#[doc(hidden)]
pub open spec fn byte_chunk_fmt<const DET: bool>() -> ByteChunkInnerFmt<DET> {
    Mapped {
        inner: Bind(
            CborHeadFmt::<DET>,
            |head: CborHead|
                match head {
                    CborHead { major: MajorType::Bytes, value: CborHeadValue::Argument(len) } => {
                        L(ExactLen(len, Tail))
                    },
                    _ => R(Void("expected a definite CBOR byte-string chunk")),
                },
        ),
        mapper: (
            |wire: ByteChunkWire|
                match wire.1 {
                    L(bytes) => bytes,
                    R(_) => arbitrary(),
                },
            |bytes: Seq<u8>|
                (
                    CborHead {
                        major: MajorType::Bytes,
                        value: CborHeadValue::Argument(bytes.len() as u64),
                    },
                    L(bytes),
                ),
        ),
    }
}

#[derive(Clone, Copy)]
pub struct ByteChunkFmt<const DET: bool>;

impl<'i, const DET: bool> Parser<&'i [u8]> for ByteChunkFmt<DET> {
    type PT = &'i [u8];

    fn parse(&self, input: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = input.len();
        let (head_len, head) = CborHeadFmt::<DET>.parse(input)?;
        match head {
            CborHead { major: MajorType::Bytes, value: CborHeadValue::Argument(len) } => {
                let rest = input.skip(head_len);
                let (content_len, bytes) = ExactLen(len, Tail).parse(&rest)?;
                Ok((head_len + content_len, bytes))
            },
            _ => Err(ParseError::custom("expected a definite CBOR byte-string chunk")),
        }
    }
}

pub type TextChunkWire = (CborHead, Sum<Seq<char>, Never>);

pub type TextChunkInnerFmt<const DET: bool> = Mapped<
    Bind<CborHeadFmt<DET>, spec_fn(CborHead) -> Sum<ExactLen<Utf8StringFmt, u64>, Void>>,
    FnSpecMapper<TextChunkWire, Seq<char>>,
>;

/// One definite text-string chunk. Each chunk validates UTF-8 independently, as RFC 8949
/// requires for indefinite-length text strings.
#[doc(hidden)]
pub open spec fn text_chunk_fmt<const DET: bool>() -> TextChunkInnerFmt<DET> {
    Mapped {
        inner: Bind(
            CborHeadFmt::<DET>,
            |head: CborHead|
                match head {
                    CborHead { major: MajorType::Text, value: CborHeadValue::Argument(len) } => {
                        L(ExactLen(len, Utf8StringFmt))
                    },
                    _ => R(Void("expected a definite CBOR text-string chunk")),
                },
        ),
        mapper: (
            |wire: TextChunkWire|
                match wire.1 {
                    L(text) => text,
                    R(_) => arbitrary(),
                },
            |text: Seq<char>|
                (
                    CborHead {
                        major: MajorType::Text,
                        value: CborHeadValue::Argument(vstd::utf8::encode_utf8(text).len() as u64),
                    },
                    L(text),
                ),
        ),
    }
}

#[derive(Clone, Copy)]
pub struct TextChunkFmt<const DET: bool>;

impl<'i, const DET: bool> Parser<&'i [u8]> for TextChunkFmt<DET> {
    type PT = &'i str;

    fn parse(&self, input: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _ = input.len();
        let (head_len, head) = CborHeadFmt::<DET>.parse(input)?;
        match head {
            CborHead { major: MajorType::Text, value: CborHeadValue::Argument(len) } => {
                let rest = input.skip(head_len);
                let (content_len, text) = ExactLen(len, Utf8StringFmt).parse(&rest)?;
                Ok((head_len + content_len, text))
            },
            _ => Err(ParseError::custom("expected a definite CBOR text-string chunk")),
        }
    }
}

#[verifier::loop_isolation(false)]
pub fn flatten_byte_chunks(chunks: Vec<&[u8]>) -> (flat: Vec<u8>)
    ensures
        flat.deep_view() == chunks.deep_view().flatten(),
{
    broadcast use vstd::seq_lib::group_seq_properties;

    let ghost chunk_views = chunks.deep_view();
    let mut flat = Vec::new();
    for i in 0..chunks.len()
        invariant
            flat.deep_view() == chunk_views.take(i as int).flatten(),
    {
        let chunk = chunks[i];
        proof {
            let prefix = chunk_views.take(i as int);
            prefix.lemma_flatten_push(chunk.deep_view());
            assert(chunk_views.take(i as int + 1) == prefix.push(chunk.deep_view()));
        }
        flat.extend_from_slice(chunk);
    }
    flat
}

pub proof fn lemma_encode_utf8_flatten(chunks: Seq<Seq<char>>)
    ensures
        vstd::utf8::encode_utf8(chunks.flatten()) == chunks.map_values(
            |chunk: Seq<char>| vstd::utf8::encode_utf8(chunk),
        ).flatten(),
    decreases chunks.len(),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::utf8::encode_utf8_concat;

    let encode = |chunk: Seq<char>| vstd::utf8::encode_utf8(chunk);
    if chunks.len() == 0 {
    } else {
        let prefix = chunks.drop_last();
        let last = chunks.last();
        lemma_encode_utf8_flatten(prefix);
        chunks.lemma_add_last_back();
        prefix.lemma_flatten_push(last);
        prefix.lemma_push_map_commute(encode, last);
        let encoded_prefix = prefix.map_values(encode);
        encoded_prefix.lemma_flatten_push(encode(last));
    }
}

#[verifier::loop_isolation(false)]
pub fn flatten_text_chunks(chunks: Vec<&str>) -> (flat: String)
    ensures
        flat.deep_view() =~= chunks.deep_view().flatten(),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::utf8::encode_utf8_valid_utf8;

    let ghost char_views = chunks.deep_view();
    let ghost byte_views = char_views.map_values(|chunk: Seq<char>| vstd::utf8::encode_utf8(chunk));
    let mut bytes = Vec::new();
    for i in 0..chunks.len()
        invariant
            bytes.deep_view() == byte_views.take(i as int).flatten(),
    {
        let chunk = chunks[i];
        let chunk_bytes = chunk.as_bytes();
        proof {
            let prefix = byte_views.take(i as int);
            prefix.lemma_flatten_push(chunk_bytes.deep_view());
            assert(chunk_bytes.deep_view() == vstd::utf8::encode_utf8(chunk.deep_view()));
            assert(byte_views.take(i as int + 1) == prefix.push(chunk_bytes.deep_view()));
        }
        bytes.extend_from_slice(chunk_bytes);
    }

    proof {
        lemma_encode_utf8_flatten(char_views);
        assert(vstd::utf8::valid_utf8(bytes.deep_view()));
    }
    // SAFETY: concatenating independently valid UTF-8 chunks remains valid UTF-8.
    let flat = unsafe { String::from_utf8_unchecked(bytes) };
    proof {
        vstd::utf8::encode_utf8_decode_utf8(char_views.flatten());
    }
    flat
}

mod derived_specs {
    use super::*;

    impl<const DET: bool> SpecParser for ByteChunkFmt<DET> {
        type PVal = Seq<u8>;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            byte_chunk_fmt::<DET>().spec_parse(input)
        }
    }

    impl<const DET: bool> Consistency for ByteChunkFmt<DET> {
        type Val = Seq<u8>;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            byte_chunk_fmt::<DET>().consistent(value)
        }
    }

    impl<const DET: bool> SpecSerializerDps for ByteChunkFmt<DET> {
        type SValue = Seq<u8>;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, out: Seq<u8>) -> Seq<u8> {
            byte_chunk_fmt::<DET>().spec_serialize_dps(value, out)
        }
    }

    impl<const DET: bool> SpecSerializer for ByteChunkFmt<DET> {
        type SVal = Seq<u8>;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            byte_chunk_fmt::<DET>().spec_serialize(value)
        }
    }

    impl<const DET: bool> SpecByteLen for ByteChunkFmt<DET> {
        type T = Seq<u8>;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            byte_chunk_fmt::<DET>().byte_len(value)
        }
    }

    impl<const DET: bool> SpecParser for TextChunkFmt<DET> {
        type PVal = Seq<char>;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            text_chunk_fmt::<DET>().spec_parse(input)
        }
    }

    impl<const DET: bool> Consistency for TextChunkFmt<DET> {
        type Val = Seq<char>;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            text_chunk_fmt::<DET>().consistent(value)
        }
    }

    impl<const DET: bool> SpecSerializerDps for TextChunkFmt<DET> {
        type SValue = Seq<char>;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, out: Seq<u8>) -> Seq<u8> {
            text_chunk_fmt::<DET>().spec_serialize_dps(value, out)
        }
    }

    impl<const DET: bool> SpecSerializer for TextChunkFmt<DET> {
        type SVal = Seq<char>;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            text_chunk_fmt::<DET>().spec_serialize(value)
        }
    }

    impl<const DET: bool> SpecByteLen for TextChunkFmt<DET> {
        type T = Seq<char>;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            text_chunk_fmt::<DET>().byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const DET: bool> SafeParser for ByteChunkFmt<DET> {
        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            byte_chunk_fmt::<DET>().lemma_parse_safe(input);
        }
    }

    impl<const DET: bool> Productive for ByteChunkFmt<DET> {
        proof fn lemma_productive(&self, input: Seq<u8>) {
            byte_chunk_fmt::<DET>().lemma_productive(input);
        }
    }

    impl SoundParser for ByteChunkFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, input: Seq<u8>) {
            byte_chunk_fmt::<true>().lemma_parse_sound_consumption(input);
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            byte_chunk_fmt::<true>().lemma_parse_sound_value(input);
        }
    }

    impl<const DET: bool> GoodSerializer for ByteChunkFmt<DET> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            byte_chunk_fmt::<DET>().lemma_serialize_len(value);
        }
    }

    impl<const DET: bool> NonTailFmt for ByteChunkFmt<DET> {
        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, out: Seq<u8>) {
            byte_chunk_fmt::<DET>().lemma_serialize_dps_prepend(value, out);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, out: Seq<u8>) {
            byte_chunk_fmt::<DET>().lemma_serialize_dps_len(value, out);
        }
    }

    impl<const DET: bool> SPRoundTripDps for ByteChunkFmt<DET> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, out: Seq<u8>) {
            byte_chunk_fmt::<DET>().theorem_serialize_dps_parse_roundtrip(value, out);
        }
    }

    impl NonMalleable for ByteChunkFmt<true> {
        proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
            byte_chunk_fmt::<true>().lemma_parse_non_malleable(left, right);
        }
    }

    impl<const DET: bool> NoLookAhead for ByteChunkFmt<DET> {
        proof fn lemma_no_lookahead(&self, left: Seq<u8>, right: Seq<u8>) {
            byte_chunk_fmt::<DET>().lemma_no_lookahead(left, right);
        }
    }

    impl<const DET: bool> EquivSerializersGeneral for ByteChunkFmt<DET> {
        proof fn lemma_serialize_equiv(&self, value: Self::SVal, out: Seq<u8>) {
            byte_chunk_fmt::<DET>().lemma_serialize_equiv(value, out);
        }
    }

    impl<const DET: bool> EquivSerializers for ByteChunkFmt<DET> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            byte_chunk_fmt::<DET>().lemma_serialize_equiv_on_empty(value);
        }
    }

    impl<const DET: bool> SafeParser for TextChunkFmt<DET> {
        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            text_chunk_fmt::<DET>().lemma_parse_safe(input);
        }
    }

    impl<const DET: bool> Productive for TextChunkFmt<DET> {
        proof fn lemma_productive(&self, input: Seq<u8>) {
            text_chunk_fmt::<DET>().lemma_productive(input);
        }
    }

    impl SoundParser for TextChunkFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, input: Seq<u8>) {
            text_chunk_fmt::<true>().lemma_parse_sound_consumption(input);
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            text_chunk_fmt::<true>().lemma_parse_sound_value(input);
        }
    }

    impl<const DET: bool> GoodSerializer for TextChunkFmt<DET> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            text_chunk_fmt::<DET>().lemma_serialize_len(value);
        }
    }

    impl<const DET: bool> NonTailFmt for TextChunkFmt<DET> {
        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, out: Seq<u8>) {
            text_chunk_fmt::<DET>().lemma_serialize_dps_prepend(value, out);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, out: Seq<u8>) {
            text_chunk_fmt::<DET>().lemma_serialize_dps_len(value, out);
        }
    }

    impl<const DET: bool> SPRoundTripDps for TextChunkFmt<DET> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, out: Seq<u8>) {
            text_chunk_fmt::<DET>().theorem_serialize_dps_parse_roundtrip(value, out);
        }
    }

    impl NonMalleable for TextChunkFmt<true> {
        proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
            text_chunk_fmt::<true>().lemma_parse_non_malleable(left, right);
        }
    }

    impl<const DET: bool> NoLookAhead for TextChunkFmt<DET> {
        proof fn lemma_no_lookahead(&self, left: Seq<u8>, right: Seq<u8>) {
            text_chunk_fmt::<DET>().lemma_no_lookahead(left, right);
        }
    }

    impl<const DET: bool> EquivSerializersGeneral for TextChunkFmt<DET> {
        proof fn lemma_serialize_equiv(&self, value: Self::SVal, out: Seq<u8>) {
            text_chunk_fmt::<DET>().lemma_serialize_equiv(value, out);
        }
    }

    impl<const DET: bool> EquivSerializers for TextChunkFmt<DET> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            text_chunk_fmt::<DET>().lemma_serialize_equiv_on_empty(value);
        }
    }

}

} // verus!
