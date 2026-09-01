//! ASN.1 BMPString values and UCS-2 contents format.
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
        uints::{exec::u16_to_be_bytes, spec::*},
        Mapped, Refined, Tail,
    },
    core::{proof::*, spec::*},
};
#[cfg(feature = "alloc")]
use alloc::string::String;
use vstd::prelude::*;
use vstd::string::StrSliceExecFns;
use OutputBuf;

verus! {

/// Semantic BMPString value. Parsing necessarily owns the result because
/// BMPString wire octets are not UTF-8 and constructed BER values may span
/// discontiguous input segments.
#[cfg(feature = "alloc")]
pub struct BmpString {
    inner: String,
}

#[verifier::ext_equal]
pub struct BmpStringSpec {
    pub inner: Seq<char>,
}

#[cfg(feature = "alloc")]
impl DeepView for BmpString {
    type V = BmpStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        BmpStringSpec { inner: self.inner.deep_view() }
    }
}

pub open spec fn is_bmp_char(c: char) -> bool {
    (c as u32) <= 0xffff
}

pub open spec fn is_valid_bmp_chars(chars: Seq<char>) -> bool {
    forall|i: int| 0 <= i < chars.len() ==> is_bmp_char(#[trigger] chars[i])
}

impl BmpStringSpec {
    pub open spec fn wf(&self) -> bool {
        is_valid_bmp_chars(self.inner)
    }
}

#[cfg(feature = "alloc")]
impl BmpString {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf()
    }

    pub fn new(inner: String) -> (res: Self)
        requires
            is_valid_bmp_chars(inner.deep_view()),
        ensures
            res.deep_view() == (BmpStringSpec { inner: inner.deep_view() }),
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

pub open spec fn bmp_code_unit(bytes: Seq<u8>, i: int) -> u32
    recommends
        0 <= 2 * i,
        2 * i + 1 < bytes.len(),
{
    u16_be_from_bytes([bytes[2 * i], bytes[2 * i + 1]]) as u32
}

/// The well-formedness condition for the BMP/UCS-2 contents octets.
pub open spec fn is_valid_bmp_string(bytes: Seq<u8>) -> bool {
    &&& bytes.len() % 2 == 0
    &&& forall|i: int|
        0 <= i < bytes.len() / 2 ==> vstd::utf8::is_scalar(#[trigger] bmp_code_unit(bytes, i))
}

/// Decode two-octet big-endian BMP/UCS-2 code units.
pub open spec fn decode_bmp_string(bytes: Seq<u8>) -> Seq<char> {
    Seq::new(bytes.len() / 2, |i: int| bmp_code_unit(bytes, i) as char)
}

/// Encode Unicode BMP scalars as two-octet big-endian BMP/UCS-2 code units.
pub open spec fn encode_bmp_string(chars: Seq<char>) -> Seq<u8> {
    Seq::new(chars.len() * 2, |i: int| u16_be_to_bytes(chars[i / 2] as u16)[i % 2])
}

proof fn lemma_scalar_char_cast(u: u32)
    requires
        vstd::utf8::is_scalar(u),
    ensures
        (u as char) as u32 == u,
{
}

proof fn lemma_bmp_char_u16_cast(c: char)
    requires
        is_bmp_char(c),
    ensures
        (c as u16) as u32 == c as u32,
{
}

proof fn lemma_encoded_bmp_code_unit(chars: Seq<char>, i: int)
    requires
        is_valid_bmp_chars(chars),
        0 <= i < chars.len(),
    ensures
        bmp_code_unit(encode_bmp_string(chars), i) == chars[i] as u32,
{
    let c = chars[i];
    let pair = u16_be_to_bytes(c as u16);
    lemma_bmp_char_u16_cast(c);
    lemma_u16_be_value_roundtrip(c as u16);
    assert(encode_bmp_string(chars)[2 * i] == pair[0]);
    assert(encode_bmp_string(chars)[2 * i + 1] == pair[1]);
}

proof fn lemma_decoded_bmp_code_unit(bytes: Seq<u8>, i: int)
    requires
        is_valid_bmp_string(bytes),
        0 <= i < bytes.len() / 2,
    ensures
        is_bmp_char(decode_bmp_string(bytes)[i]),
        u16_be_to_bytes(decode_bmp_string(bytes)[i] as u16) == [bytes[2 * i], bytes[2 * i + 1]],
{
    let unit = bmp_code_unit(bytes, i);
    let pair = [bytes[2 * i], bytes[2 * i + 1]];
    let code = u16_be_from_bytes(pair);
    assert(vstd::utf8::is_scalar(unit));
    lemma_scalar_char_cast(unit);
    lemma_u16_be_bytes_roundtrip(pair);
    lemma_bmp_char_u16_cast(unit as char);
}

pub proof fn lemma_encode_bmp_string_valid(chars: Seq<char>)
    requires
        is_valid_bmp_chars(chars),
    ensures
        is_valid_bmp_string(encode_bmp_string(chars)),
{
    let bytes = encode_bmp_string(chars);
    assert(bytes.len() % 2 == 0);
    assert forall|i: int| 0 <= i < bytes.len() / 2 implies vstd::utf8::is_scalar(
        #[trigger] bmp_code_unit(bytes, i),
    ) by {
        let c = chars[i];
        vstd::utf8::char_is_scalar(c);
        lemma_encoded_bmp_code_unit(chars, i);
    }
}

pub proof fn lemma_decode_encode_bmp_string(chars: Seq<char>)
    requires
        is_valid_bmp_chars(chars),
    ensures
        decode_bmp_string(encode_bmp_string(chars)) == chars,
{
    let bytes = encode_bmp_string(chars);
    assert(decode_bmp_string(bytes).len() == chars.len());
    assert forall|i: int| 0 <= i < chars.len() implies #[trigger] decode_bmp_string(bytes)[i]
        == chars[i] by {
        lemma_encoded_bmp_code_unit(chars, i);
        vstd::utf8::char_u32_cast(chars[i], bmp_code_unit(bytes, i));
    }
}

pub proof fn lemma_encode_decode_bmp_string(bytes: Seq<u8>)
    requires
        is_valid_bmp_string(bytes),
    ensures
        encode_bmp_string(decode_bmp_string(bytes)) == bytes,
{
    let chars = decode_bmp_string(bytes);
    assert(encode_bmp_string(chars).len() == bytes.len());
    assert forall|i: int| 0 <= i < bytes.len() implies #[trigger] encode_bmp_string(chars)[i]
        == bytes[i] by {
        let unit_index = i / 2;
        lemma_decoded_bmp_code_unit(bytes, unit_index);
    }
}

pub proof fn lemma_decoded_bmp_string_valid(bytes: Seq<u8>)
    requires
        is_valid_bmp_string(bytes),
    ensures
        is_valid_bmp_chars(decode_bmp_string(bytes)),
{
    assert forall|i: int| 0 <= i < decode_bmp_string(bytes).len() implies is_bmp_char(
        #[trigger] decode_bmp_string(bytes)[i],
    ) by {
        lemma_decoded_bmp_code_unit(bytes, i);
    }
}

type BmpStringInnerFmt = Mapped<
    Refined<Tail, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, BmpStringSpec>,
>;

pub open spec fn bmpstring_fmt() -> BmpStringInnerFmt {
    Mapped {
        inner: Refined(Tail, |bytes: Seq<u8>| is_valid_bmp_string(bytes)),
        mapper: (
            |bytes: Seq<u8>| BmpStringSpec { inner: decode_bmp_string(bytes) },
            |s: BmpStringSpec| encode_bmp_string(s.inner),
        ),
    }
}

proof fn lemma_bmpstring_fmt_sound_nonmal_inv()
    ensures
        bmpstring_fmt().sound_inv(),
        bmpstring_fmt().nonmal_inv(),
{
    assert forall|bytes: Seq<u8>| #[trigger] is_valid_bmp_string(bytes) implies encode_bmp_string(
        decode_bmp_string(bytes),
    ) == bytes by {
        lemma_encode_decode_bmp_string(bytes);
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for super::super::BmpStringFmt {
        type PVal = BmpStringSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            bmpstring_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for super::super::BmpStringFmt {
        type Val = BmpStringSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            bmpstring_fmt().consistent(v) && v.wf()
        }
    }

    impl SpecSerializerDps for super::super::BmpStringFmt {
        type SValue = BmpStringSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            bmpstring_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for super::super::BmpStringFmt {
        type SVal = BmpStringSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            bmpstring_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for super::super::BmpStringFmt {
        type T = BmpStringSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            bmpstring_fmt().byte_len(v)
        }
    }

}

pub(crate) proof fn lemma_bmp_string_fmt_serialization(value: BmpStringSpec)
    ensures
        super::BmpStringFmt.spec_serialize(value) == encode_bmp_string(value.inner),
        super::BmpStringFmt.byte_len(value) == value.inner.len() * 2,
{
}

mod derived_proofs {
    use super::*;

    impl SafeParser for super::super::BmpStringFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            bmpstring_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for super::super::BmpStringFmt {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, _s: Seq<u8>) {
        }
    }

    impl SoundParser for super::super::BmpStringFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_bmpstring_fmt_sound_nonmal_inv();
            bmpstring_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_bmpstring_fmt_sound_nonmal_inv();
            bmpstring_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for super::super::BmpStringFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            bmpstring_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for super::super::BmpStringFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_encode_bmp_string_valid(v.inner);
            lemma_decode_encode_bmp_string(v.inner);
            let bytes = encode_bmp_string(v.inner);
            let inner = Refined(Tail, |bytes: Seq<u8>| is_valid_bmp_string(bytes));
            inner.theorem_serialize_dps_parse_roundtrip(bytes, obuf);
        }
    }

    impl NonMalleable for super::super::BmpStringFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_bmpstring_fmt_sound_nonmal_inv();
            bmpstring_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for super::super::BmpStringFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            bmpstring_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

/// Check that a byte slice is a valid BMPString without allocation.
/// TODO: Verify this function while keeping it efficient and idiomatic.
#[verifier::external_body]
pub fn check_valid_bmp_string(bytes: &[u8]) -> (res: bool)
    ensures
        res == is_valid_bmp_string(bytes.deep_view()),
{
    if bytes.len() % 2 != 0 {
        return false;
    }
    bytes.chunks_exact(2).map(|pair| u16::from_be_bytes([pair[0], pair[1]]) as u32).all(
        |unit| char::from_u32(unit).is_some(),
    )
}

/// Decode a byte slice into a String, assuming it contains a valid BMPString.
/// TODO: Verify this function while keeping it efficient and idiomatic.
#[cfg(feature = "alloc")]
#[verifier::external_body]
fn decode_bmp_string_owned(bytes: &[u8]) -> (res: String)
    requires
        is_valid_bmp_string(bytes.deep_view()),
    ensures
        res.deep_view() == decode_bmp_string(bytes.deep_view()),
{
    // SAFETY: `is_valid_bmp_string` guarantees that all code units are valid BMP scalars, which are valid Unicode code points, so `char::from_u32_unchecked` is safe to use here.
    bytes.chunks_exact(2).map(
        |pair| unsafe { char::from_u32_unchecked(u16::from_be_bytes([pair[0], pair[1]]) as u32) },
    ).collect()
}

#[cfg(feature = "alloc")]
impl<'i> Parser<&'i [u8]> for super::BmpStringFmt {
    type PT = BmpString;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if !check_valid_bmp_string(bytes) {
            Err(ParseError::custom("Invalid BMPString"))
        } else {
            let inner = decode_bmp_string_owned(bytes);
            Ok((n, BmpString::new(inner)))
        }
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf> Serializer<Output, BmpString> for super::BmpStringFmt {
    #[verifier::loop_isolation(false)]
    fn serialize_into(&self, v: &BmpString, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        proof {
            use_type_invariant(v);
            lemma_encode_bmp_string_valid(v.deep_view().inner);
        }
        let value = v.inner.as_str();

        let ghost initial = obuf@;
        let len = value.unicode_len();
        for i in 0..len
            invariant
                obuf@ == initial + encode_bmp_string(value.deep_view().take(i as int)),
                forall|n| old(obuf).fits(2 * i as nat + n) <==> obuf.fits(n),
                old(obuf).same_destination(obuf),
        {
            proof {
                old(obuf).lemma_fits_mono(2 * i as nat + 2, 2 * len as nat);
            }
            let c = value.get_char(i);
            let pair = u16_to_be_bytes(c as u16);
            obuf.write_bytes(&pair);
        }
    }
}

#[cfg(feature = "alloc")]
impl Prepare<BmpString> for super::BmpStringFmt {
    fn prepare(&self, v: &BmpString) -> Result<usize, PreSerializeError> {
        proof {
            use_type_invariant(v);
            lemma_encode_bmp_string_valid(v.deep_view().inner);
        }
        v.inner.as_str().unicode_len().checked_mul(2).ok_or(PreSerializeError::length_too_large())
    }
}

#[cfg(feature = "alloc")]
impl ByteLen<BmpString> for super::BmpStringFmt {
    fn length(&self, v: &BmpString) -> usize {
        proof {
            use_type_invariant(v);
        }
        v.inner.as_str().unicode_len() * 2
    }
}

} // verus!
