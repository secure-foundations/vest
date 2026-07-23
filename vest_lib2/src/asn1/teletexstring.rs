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
#[cfg(feature = "alloc")]
use alloc::string::String;
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;
use OutputBuf;

verus! {

pub struct TeletexString<'a> {
    inner: &'a str,
}

/// Owned TeletexString value used when BER segments must be flattened.
#[cfg(feature = "alloc")]
pub struct TeletexStringOwned {
    inner: String,
}

#[verifier::ext_equal]
pub struct TeletexStringSpec {
    pub inner: Seq<char>,
}

impl<'a> DeepView for TeletexString<'a> {
    type V = TeletexStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        TeletexStringSpec { inner: self.inner.deep_view() }
    }
}

#[cfg(feature = "alloc")]
impl DeepView for TeletexStringOwned {
    type V = TeletexStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        TeletexStringSpec { inner: self.inner.deep_view() }
    }
}

impl<'a> TeletexString<'a> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf()
    }

    pub fn new(inner: &'a str) -> (res: Self)
        requires
            is_valid_teletex_string_spec(vstd::utf8::encode_utf8(inner.deep_view())),
        ensures
            res.deep_view() == (TeletexStringSpec { inner: inner.deep_view() }),
    {
        TeletexString { inner }
    }

    pub fn inner(&self) -> (res: &'a str)
        ensures
            res.deep_view() == self.deep_view().inner,
    {
        self.inner
    }
}

#[cfg(feature = "alloc")]
impl TeletexStringOwned {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf()
    }

    pub fn new(inner: String) -> (res: Self)
        requires
            is_valid_teletex_string_spec(vstd::utf8::encode_utf8(inner.deep_view())),
        ensures
            res.deep_view() == (TeletexStringSpec { inner: inner.deep_view() }),
    {
        Self { inner }
    }

    pub fn inner(&self) -> (res: &str)
        ensures
            res.deep_view() == self.deep_view().inner,
    {
        self.inner.as_str()
    }
}

impl TeletexStringSpec {
    pub open spec fn wf(&self) -> bool {
        is_valid_teletex_string_spec(vstd::utf8::encode_utf8(self.inner))
    }
}

/// TODO: Specify the actual validation logic for TeletexString.
pub open spec fn is_valid_teletex_string_spec(bytes: Seq<u8>) -> bool {
    true
}

/// TODO: Implement the actual validation logic for TeletexString.
pub fn is_valid_teletex_string(_bytes: &[u8]) -> (res: bool)
    ensures
        res == is_valid_teletex_string_spec(_bytes.deep_view()),
{
    true
}

type TeletexStringFmt = Mapped<
    Refined<Tail, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, TeletexStringSpec>,
>;

pub open spec fn teletexstring_fmt() -> TeletexStringFmt {
    Mapped {
        inner: Refined(
            Tail,
            |bytes: Seq<u8>| is_valid_teletex_string_spec(bytes) && vstd::utf8::valid_utf8(bytes),
        ),
        mapper: (
            |bytes: Seq<u8>| TeletexStringSpec { inner: vstd::utf8::decode_utf8(bytes) },
            |s: TeletexStringSpec| vstd::utf8::encode_utf8(s.inner),
        ),
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for super::super::TeletexStringFmt {
        type PVal = TeletexStringSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            teletexstring_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for super::super::TeletexStringFmt {
        type Val = TeletexStringSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            teletexstring_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for super::super::TeletexStringFmt {
        type SValue = TeletexStringSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            teletexstring_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for super::super::TeletexStringFmt {
        type SVal = TeletexStringSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            teletexstring_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for super::super::TeletexStringFmt {
        type T = TeletexStringSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            teletexstring_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for super::super::TeletexStringFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            teletexstring_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for super::super::TeletexStringFmt {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
        }
    }

    impl SoundParser for super::super::TeletexStringFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            teletexstring_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            teletexstring_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for super::super::TeletexStringFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            teletexstring_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for super::super::TeletexStringFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            broadcast use vstd::utf8::encode_utf8_decode_utf8;

            teletexstring_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for super::super::TeletexStringFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            teletexstring_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for super::super::TeletexStringFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            teletexstring_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i> Parser<&'i [u8]> for super::TeletexStringFmt {
    type PT = TeletexString<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if !is_valid_teletex_string(bytes) {
            Err(ParseError::custom("Invalid TeletexString"))
        } else if !is_valid_utf8(bytes) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            let inner = utf8_from_bytes_unchecked(bytes);
            Ok((n, TeletexString::new(inner)))
        }
    }
}

impl<Output: OutputBuf, 'i> Serializer<Output, TeletexString<'i>> for super::TeletexStringFmt {
    fn serialize_into(&self, v: &TeletexString<'i>, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.serialize_into(&bytes, obuf);
    }
}

impl<'i> Prepare<TeletexString<'i>> for super::TeletexStringFmt {
    fn prepare(&self, v: &TeletexString<'i>) -> Result<usize, PreSerializeError> {
        broadcast use vstd::utf8::encode_utf8_valid_utf8;

        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.prepare(&bytes)
    }
}

impl<'i> ByteLen<TeletexString<'i>> for super::TeletexStringFmt {
    fn length(&self, v: &TeletexString<'i>) -> usize {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.length(&bytes)
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf> Serializer<Output, TeletexStringOwned> for super::TeletexStringFmt {
    fn serialize_into(&self, v: &TeletexStringOwned, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_str().as_bytes();
        Tail.serialize_into(&bytes, obuf);
    }
}

#[cfg(feature = "alloc")]
impl Prepare<TeletexStringOwned> for super::TeletexStringFmt {
    fn prepare(&self, v: &TeletexStringOwned) -> Result<usize, PreSerializeError> {
        broadcast use vstd::utf8::encode_utf8_valid_utf8;

        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_str().as_bytes();
        Tail.prepare(&bytes)
    }
}

#[cfg(feature = "alloc")]
impl ByteLen<TeletexStringOwned> for super::TeletexStringFmt {
    fn length(&self, v: &TeletexStringOwned) -> usize {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_str().as_bytes();
        Tail.length(&bytes)
    }
}

} // verus!
