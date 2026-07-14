use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::{
    combinators::{mapped::spec::FnSpecMapper, Mapped, Refined, Tail},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;
use OutputBuf;

verus! {

pub type Utf8String<'a> = &'a str;

#[verifier::external_body]
pub fn is_valid_utf8(bytes: &[u8]) -> (res: bool)
    ensures
        res == vstd::utf8::valid_utf8(bytes.deep_view()),
{
    str::from_utf8(bytes).is_ok()
}

pub fn utf8_from_bytes_unchecked<'a>(bytes: &'a [u8]) -> (res: &'a str)
    requires
        vstd::utf8::valid_utf8(bytes.deep_view()),
    ensures
        res.spec_bytes() == bytes.deep_view(),
        res.deep_view() == vstd::utf8::decode_utf8(bytes.deep_view()),
{
    broadcast use vstd::utf8::decode_utf8_encode_utf8;
    broadcast use vstd::utf8::encode_utf8_decode_utf8;

    assert(bytes@ == bytes.deep_view());
    // SAFETY: Verus ensures that the bytes are valid UTF-8 :p
    unsafe { str::from_utf8_unchecked(bytes) }
}

type Utf8StringFmt = Mapped<Refined<Tail, PredFnSpec<Seq<u8>>>, FnSpecMapper<Seq<u8>, Seq<char>>>;

pub open spec fn utf8string_fmt() -> Utf8StringFmt {
    Mapped {
        inner: Refined(Tail, |bytes: Seq<u8>| vstd::utf8::valid_utf8(bytes)),
        mapper: (
            |bytes: Seq<u8>| vstd::utf8::decode_utf8(bytes),
            |chars: Seq<char>| vstd::utf8::encode_utf8(chars),
        ),
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for super::super::Utf8String {
        type PVal = Seq<char>;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            utf8string_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for super::super::Utf8String {
        type Val = Seq<char>;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            utf8string_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for super::super::Utf8String {
        type SValue = Seq<char>;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            utf8string_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for super::super::Utf8String {
        type SVal = Seq<char>;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            utf8string_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for super::super::Utf8String {
        type T = Seq<char>;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            utf8string_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for super::super::Utf8String {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            utf8string_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for super::super::Utf8String {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
        }
    }

    impl SoundParser for super::super::Utf8String {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            utf8string_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            utf8string_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for super::super::Utf8String {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            utf8string_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for super::super::Utf8String {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            broadcast use vstd::utf8::encode_utf8_decode_utf8;

            utf8string_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for super::super::Utf8String {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            utf8string_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for super::super::Utf8String {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            utf8string_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i> Parser<&'i [u8]> for super::Utf8String {
    type PT = &'i str;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if is_valid_utf8(bytes) {
            let inner = utf8_from_bytes_unchecked(bytes);
            Ok((n, inner))
        } else {
            Err(ParseError::custom("Invalid UTF-8"))
        }
    }
}

impl<Output: OutputBuf + ?Sized, 'i> Serializer<Output, &'i str> for super::Utf8String {
    fn serialize_into(&self, v: &&'i str, obuf: &mut Output) {
        let bytes = v.as_bytes();
        Tail.serialize_into(&bytes, obuf);
    }
}

impl<'i> Prepare<&'i str> for super::Utf8String {
    fn prepare(&self, v: &&'i str) -> Result<usize, PreSerializeError> {
        broadcast use vstd::utf8::encode_utf8_valid_utf8;

        let bytes = v.as_bytes();
        Tail.prepare(&bytes)
    }
}

impl<'i> ByteLen<&'i str> for super::Utf8String {
    fn length(&self, v: &&'i str) -> usize {
        let bytes = v.as_bytes();
        Tail.length(&bytes)
    }
}

} // verus!
