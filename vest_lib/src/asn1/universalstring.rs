//! ASN.1 UniversalString contents.
//!
//! UniversalString represents ISO/IEC 10646 scalar values as four-octet,
//! big-endian code points. Its semantic Rust value is an owned `String`
//! because the wire representation is not UTF-8.
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::{
    combinators::{
        mapped::spec::FnSpecMapper,
        uints::{exec::u32_to_be_bytes, spec::*},
        Mapped, Refined, Tail,
    },
    core::{proof::*, spec::*},
};
#[cfg(feature = "alloc")]
use alloc::string::String;
use vstd::prelude::*;
#[cfg(feature = "alloc")]
use vstd::string::StrSliceExecFns;
use OutputBuf;

verus! {

#[cfg(feature = "alloc")]
pub type UniversalString = String;

pub type UniversalStringSpec = Seq<char>;

pub open spec fn universal_code_point(bytes: Seq<u8>, i: int) -> u32
    recommends
        0 <= 4 * i,
        4 * i + 3 < bytes.len(),
{
    u32_be_from_bytes([bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]])
}

/// The well-formedness condition for UniversalString contents octets.
pub open spec fn is_valid_universal_string(bytes: Seq<u8>) -> bool {
    &&& bytes.len() % 4 == 0
    &&& forall|i: int|
        0 <= i < bytes.len() / 4 ==> vstd::utf8::is_scalar(
            #[trigger] universal_code_point(bytes, i),
        )
}

/// Decode four-octet big-endian ISO/IEC 10646 scalar values.
pub open spec fn decode_universal_string(bytes: Seq<u8>) -> Seq<char> {
    Seq::new(bytes.len() / 4, |i: int| universal_code_point(bytes, i) as char)
}

/// Encode Unicode scalar values as four-octet big-endian code points.
pub open spec fn encode_universal_string(chars: Seq<char>) -> Seq<u8> {
    Seq::new(chars.len() * 4, |i: int| u32_be_to_bytes(chars[i / 4] as u32)[i % 4])
}

proof fn lemma_scalar_char_cast(u: u32)
    requires
        vstd::utf8::is_scalar(u),
    ensures
        (u as char) as u32 == u,
{
}

proof fn lemma_encoded_universal_code_point(chars: Seq<char>, i: int)
    requires
        0 <= i < chars.len(),
    ensures
        universal_code_point(encode_universal_string(chars), i) == chars[i] as u32,
{
    let c = chars[i];
    let word = u32_be_to_bytes(c as u32);
    lemma_u32_be_value_roundtrip(c as u32);
    assert(encode_universal_string(chars)[4 * i] == word[0]);
    assert(encode_universal_string(chars)[4 * i + 1] == word[1]);
    assert(encode_universal_string(chars)[4 * i + 2] == word[2]);
    assert(encode_universal_string(chars)[4 * i + 3] == word[3]);
}

proof fn lemma_decoded_universal_code_point(bytes: Seq<u8>, i: int)
    requires
        is_valid_universal_string(bytes),
        0 <= i < bytes.len() / 4,
    ensures
        u32_be_to_bytes(decode_universal_string(bytes)[i] as u32) == [
            bytes[4 * i],
            bytes[4 * i + 1],
            bytes[4 * i + 2],
            bytes[4 * i + 3],
        ],
{
    let word = [bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]];
    let code = u32_be_from_bytes(word);
    assert(code == universal_code_point(bytes, i));
    assert(vstd::utf8::is_scalar(code));
    lemma_scalar_char_cast(code);
    lemma_u32_be_bytes_roundtrip(word);
}

pub proof fn lemma_encode_universal_string_valid(chars: Seq<char>)
    ensures
        is_valid_universal_string(encode_universal_string(chars)),
{
    let bytes = encode_universal_string(chars);
    assert(bytes.len() % 4 == 0);
    assert forall|i: int| 0 <= i < bytes.len() / 4 implies vstd::utf8::is_scalar(
        #[trigger] universal_code_point(bytes, i),
    ) by {
        vstd::utf8::char_is_scalar(chars[i]);
        lemma_encoded_universal_code_point(chars, i);
    }
}

pub proof fn lemma_decode_encode_universal_string(chars: Seq<char>)
    ensures
        decode_universal_string(encode_universal_string(chars)) == chars,
{
    let bytes = encode_universal_string(chars);
    assert(decode_universal_string(bytes).len() == chars.len());
    assert forall|i: int| 0 <= i < chars.len() implies #[trigger] decode_universal_string(bytes)[i]
        == chars[i] by {
        lemma_encoded_universal_code_point(chars, i);
        vstd::utf8::char_u32_cast(chars[i], universal_code_point(bytes, i));
    }
}

pub proof fn lemma_encode_decode_universal_string(bytes: Seq<u8>)
    requires
        is_valid_universal_string(bytes),
    ensures
        encode_universal_string(decode_universal_string(bytes)) == bytes,
{
    let chars = decode_universal_string(bytes);
    assert(encode_universal_string(chars).len() == bytes.len());
    assert forall|i: int| 0 <= i < bytes.len() implies #[trigger] encode_universal_string(chars)[i]
        == bytes[i] by {
        lemma_decoded_universal_code_point(bytes, i / 4);
    }
}

type UniversalStringInnerFmt = Mapped<
    Refined<Tail, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, Seq<char>>,
>;

pub open spec fn universalstring_fmt() -> UniversalStringInnerFmt {
    Mapped {
        inner: Refined(Tail, |bytes: Seq<u8>| is_valid_universal_string(bytes)),
        mapper: (
            |bytes: Seq<u8>| decode_universal_string(bytes),
            |chars: Seq<char>| encode_universal_string(chars),
        ),
    }
}

proof fn lemma_universalstring_fmt_sound_nonmal_inv()
    ensures
        universalstring_fmt().sound_inv(),
        universalstring_fmt().nonmal_inv(),
{
    assert forall|bytes: Seq<u8>| #[trigger]
        is_valid_universal_string(bytes) implies encode_universal_string(
        decode_universal_string(bytes),
    ) == bytes by {
        lemma_encode_decode_universal_string(bytes);
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for super::super::UniversalStringFmt {
        type PVal = Seq<char>;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            universalstring_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for super::super::UniversalStringFmt {
        type Val = Seq<char>;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            universalstring_fmt().consistent(value)
        }
    }

    impl SpecSerializerDps for super::super::UniversalStringFmt {
        type SValue = Seq<char>;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            universalstring_fmt().spec_serialize_dps(value, obuf)
        }
    }

    impl SpecSerializer for super::super::UniversalStringFmt {
        type SVal = Seq<char>;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            universalstring_fmt().spec_serialize(value)
        }
    }

    impl SpecByteLen for super::super::UniversalStringFmt {
        type T = Seq<char>;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            universalstring_fmt().byte_len(value)
        }
    }

}

pub(crate) proof fn lemma_universal_string_fmt_serialization(value: Seq<char>)
    ensures
        super::UniversalStringFmt.spec_serialize(value) == encode_universal_string(value),
        super::UniversalStringFmt.byte_len(value) == value.len() * 4,
{
}

mod derived_proofs {
    use super::*;

    impl SafeParser for super::super::UniversalStringFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            universalstring_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for super::super::UniversalStringFmt {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, _input: Seq<u8>) {
        }
    }

    impl SoundParser for super::super::UniversalStringFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_universalstring_fmt_sound_nonmal_inv();
            universalstring_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_universalstring_fmt_sound_nonmal_inv();
            universalstring_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for super::super::UniversalStringFmt {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            universalstring_fmt().lemma_serialize_len(value);
        }
    }

    impl SPRoundTripDps for super::super::UniversalStringFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            lemma_encode_universal_string_valid(value);
            lemma_decode_encode_universal_string(value);
            let bytes = encode_universal_string(value);
            let inner = Refined(Tail, |bytes: Seq<u8>| is_valid_universal_string(bytes));
            inner.theorem_serialize_dps_parse_roundtrip(bytes, obuf);
        }
    }

    impl NonMalleable for super::super::UniversalStringFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_universalstring_fmt_sound_nonmal_inv();
            universalstring_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for super::super::UniversalStringFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            universalstring_fmt().lemma_serialize_equiv_on_empty(value);
        }
    }

}

#[verifier::external_body]
/// Check a UniversalString contents slice without allocation.
pub fn check_valid_universal_string(bytes: &[u8]) -> (valid: bool)
    ensures
        valid == is_valid_universal_string(bytes.deep_view()),
{
    if bytes.len() % 4 != 0 {
        return false;
    }
    bytes.chunks_exact(4).map(|word| u32::from_be_bytes([word[0], word[1], word[2], word[3]])).all(
        |code| char::from_u32(code).is_some(),
    )
}

#[cfg(feature = "alloc")]
#[verifier::external_body]
pub(crate) fn decode_universal_string_owned(bytes: &[u8]) -> (value: String)
    requires
        is_valid_universal_string(bytes.deep_view()),
    ensures
        value.deep_view() == decode_universal_string(bytes.deep_view()),
{
    bytes.chunks_exact(4).map(
        |word|
            unsafe {
                char::from_u32_unchecked(u32::from_be_bytes([word[0], word[1], word[2], word[3]]))
            },
    ).collect()
}

#[cfg(feature = "alloc")]
impl<'i> Parser<&'i [u8]> for super::UniversalStringFmt {
    type PT = UniversalString;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if !check_valid_universal_string(bytes) {
            Err(ParseError::custom("Invalid UniversalString"))
        } else {
            Ok((n, decode_universal_string_owned(bytes)))
        }
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf> Serializer<Output, UniversalString> for super::UniversalStringFmt {
    #[verifier::loop_isolation(false)]
    fn serialize_into(&self, value: &UniversalString, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        proof {
            lemma_encode_universal_string_valid(value.deep_view());
        }
        let value = value.as_str();

        let ghost initial = obuf@;
        let len = value.unicode_len();
        for i in 0..len
            invariant
                obuf@ == initial + encode_universal_string(value.deep_view().take(i as int)),
                forall|n| old(obuf).fits(4 * i as nat + n) <==> obuf.fits(n),
                old(obuf).same_destination(obuf),
        {
            proof {
                old(obuf).lemma_fits_mono(4 * i as nat + 4, 4 * len as nat);
            }
            let c = value.get_char(i);
            let word = u32_to_be_bytes(c as u32);
            obuf.write_bytes(&word);
        }
    }
}

#[cfg(feature = "alloc")]
impl Prepare<UniversalString> for super::UniversalStringFmt {
    fn prepare(&self, value: &UniversalString) -> Result<usize, PreSerializeError> {
        proof {
            lemma_encode_universal_string_valid(value.deep_view());
        }
        value.as_str().unicode_len().checked_mul(4).ok_or(PreSerializeError::length_too_large())
    }
}

#[cfg(feature = "alloc")]
impl ByteLen<UniversalString> for super::UniversalStringFmt {
    fn length(&self, value: &UniversalString) -> usize {
        value.as_str().unicode_len() * 4
    }
}

} // verus!
