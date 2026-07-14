use super::utf8string::{is_valid_utf8, utf8_from_bytes_unchecked};
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

pub struct BmpString<'a> {
    inner: &'a str,
}

#[verifier::ext_equal]
pub struct BmpStringSpec {
    pub inner: Seq<char>,
}

impl<'a> DeepView for BmpString<'a> {
    type V = BmpStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        BmpStringSpec { inner: self.inner.deep_view() }
    }
}

impl<'a> BmpString<'a> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf()
    }

    pub fn new(inner: &'a str) -> (res: Self)
        requires
            is_valid_bmp_string_spec(vstd::utf8::encode_utf8(inner.deep_view())),
        ensures
            res.deep_view() == (BmpStringSpec { inner: inner.deep_view() }),
    {
        BmpString { inner }
    }

    pub fn inner(&self) -> (res: &'a str)
        ensures
            res.deep_view() == self.deep_view().inner,
    {
        self.inner
    }
}

impl BmpStringSpec {
    pub open spec fn wf(&self) -> bool {
        is_valid_bmp_string_spec(vstd::utf8::encode_utf8(self.inner))
    }
}

pub open spec fn is_valid_bmp_string_spec(bytes: Seq<u8>) -> bool {
    bytes.len() % 2 == 0
}

pub fn is_valid_bmp_string(bytes: &[u8]) -> (res: bool)
    ensures
        res == is_valid_bmp_string_spec(bytes.deep_view()),
{
    bytes.len() % 2 == 0
}

type BmpStringFmt = Mapped<
    Refined<Tail, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, BmpStringSpec>,
>;

pub open spec fn bmpstring_fmt() -> BmpStringFmt {
    Mapped {
        inner: Refined(
            Tail,
            |bytes: Seq<u8>| is_valid_bmp_string_spec(bytes) && vstd::utf8::valid_utf8(bytes),
        ),
        mapper: (
            |bytes: Seq<u8>| BmpStringSpec { inner: vstd::utf8::decode_utf8(bytes) },
            |s: BmpStringSpec| vstd::utf8::encode_utf8(s.inner),
        ),
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for super::super::BmpString {
        type PVal = BmpStringSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            bmpstring_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for super::super::BmpString {
        type Val = BmpStringSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            bmpstring_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for super::super::BmpString {
        type SValue = BmpStringSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            bmpstring_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for super::super::BmpString {
        type SVal = BmpStringSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            bmpstring_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for super::super::BmpString {
        type T = BmpStringSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            bmpstring_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for super::super::BmpString {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            bmpstring_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for super::super::BmpString {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
        }
    }

    impl SoundParser for super::super::BmpString {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            bmpstring_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            bmpstring_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for super::super::BmpString {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            bmpstring_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for super::super::BmpString {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            broadcast use vstd::utf8::encode_utf8_decode_utf8;

            bmpstring_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for super::super::BmpString {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            bmpstring_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for super::super::BmpString {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            bmpstring_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i> Parser<&'i [u8]> for super::BmpString {
    type PT = BmpString<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if !is_valid_bmp_string(bytes) {
            Err(ParseError::custom("Invalid BmpString"))
        } else if !is_valid_utf8(bytes) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            let inner = utf8_from_bytes_unchecked(bytes);
            Ok((n, BmpString::new(inner)))
        }
    }
}

impl<Output: OutputBuf + ?Sized, 'i> Serializer<Output, BmpString<'i>> for super::BmpString {
    fn serialize_into(&self, v: &BmpString<'i>, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.serialize_into(&bytes, obuf);
    }
}

impl<'i> Prepare<BmpString<'i>> for super::BmpString {
    fn prepare(&self, v: &BmpString<'i>) -> Result<usize, PreSerializeError> {
        broadcast use vstd::utf8::encode_utf8_valid_utf8;

        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.prepare(&bytes)
    }
}

impl<'i> ByteLen<BmpString<'i>> for super::BmpString {
    fn length(&self, v: &BmpString<'i>) -> usize {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.length(&bytes)
    }
}

} // verus!
