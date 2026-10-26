//! ASN.1 PrintableString borrowed and owned values and contents format.
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

verus! {

pub struct PrintableString<'a> {
    inner: &'a str,
}

/// Owned PrintableString value used when the wire representation is assembled
/// from multiple BER segments.
#[cfg(feature = "alloc")]
pub struct PrintableStringOwned {
    inner: String,
}

#[verifier::ext_equal]
pub struct PrintableStringSpec {
    pub inner: Seq<char>,
}

impl<'a> DeepView for PrintableString<'a> {
    type V = PrintableStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        PrintableStringSpec { inner: self.inner.deep_view() }
    }
}

#[cfg(feature = "alloc")]
impl DeepView for PrintableStringOwned {
    type V = PrintableStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        PrintableStringSpec { inner: self.inner.deep_view() }
    }
}

impl<'a> PrintableString<'a> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf()
    }

    pub fn new(inner: &'a str) -> (res: Self)
        requires
            is_valid_printable_string_spec(vstd::utf8::encode_utf8(inner.deep_view())),
        ensures
            res.deep_view() == (PrintableStringSpec { inner: inner.deep_view() }),
    {
        PrintableString { inner }
    }

    pub fn inner(&self) -> (res: &'a str)
        ensures
            res.deep_view() == self.deep_view().inner,
    {
        self.inner
    }
}

#[cfg(feature = "alloc")]
impl PrintableStringOwned {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf()
    }

    pub fn new(inner: String) -> (res: Self)
        requires
            is_valid_printable_string_spec(vstd::utf8::encode_utf8(inner.deep_view())),
        ensures
            res.deep_view() == (PrintableStringSpec { inner: inner.deep_view() }),
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

impl PrintableStringSpec {
    pub open spec fn wf(&self) -> bool {
        is_valid_printable_string_spec(vstd::utf8::encode_utf8(self.inner))
    }
}

/// Tests membership in PrintableString's ASCII repertoire.
#[verifier::allow_in_spec]
pub fn is_printable_byte(b: u8) -> bool
    returns
        matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9'
            | b' ' | b'\'' | b'(' | b')' | b'+' | b',' | b'-' | b'.' | b'/'
            | b':' | b'=' | b'?'),
{
    matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9'
        | b' ' | b'\'' | b'(' | b')' | b'+' | b',' | b'-' | b'.' | b'/'
        | b':' | b'=' | b'?')
}

pub open spec fn is_valid_printable_string_spec(bytes: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < bytes.len() ==> is_printable_byte(#[trigger] bytes[i])
}

/// Checks PrintableString contents without allocation.
#[verifier::allow_in_spec]
pub fn is_valid_printable_string(bytes: &[u8]) -> (res: bool)
    returns
        is_valid_printable_string_spec(bytes.deep_view()),
{
    assert(bytes@ == bytes.deep_view());
    bytes.iter().all(
        |&b: &u8| -> (valid: bool)
            ensures
                valid == is_printable_byte(b),
            { is_printable_byte(b) },
    )
}

type PrintableStringFmt = Mapped<
    Refined<Tail, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, PrintableStringSpec>,
>;

pub open spec fn printablestring_fmt() -> PrintableStringFmt {
    Mapped {
        inner: Refined(
            Tail,
            |bytes: Seq<u8>| is_valid_printable_string_spec(bytes) && vstd::utf8::valid_utf8(bytes),
        ),
        mapper: (
            |bytes: Seq<u8>| PrintableStringSpec { inner: vstd::utf8::decode_utf8(bytes) },
            |s: PrintableStringSpec| vstd::utf8::encode_utf8(s.inner),
        ),
    }
}

mod derived_specs {
    use super::*;

    impl SpecParser for super::super::PrintableStringFmt {
        type PVal = PrintableStringSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            printablestring_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for super::super::PrintableStringFmt {
        type Val = PrintableStringSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            printablestring_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for super::super::PrintableStringFmt {
        type SValue = PrintableStringSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            printablestring_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for super::super::PrintableStringFmt {
        type SVal = PrintableStringSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            printablestring_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for super::super::PrintableStringFmt {
        type T = PrintableStringSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            printablestring_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for super::super::PrintableStringFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            printablestring_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for super::super::PrintableStringFmt {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
        }
    }

    impl SoundParser for super::super::PrintableStringFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            printablestring_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            printablestring_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for super::super::PrintableStringFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            printablestring_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for super::super::PrintableStringFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            broadcast use vstd::utf8::encode_utf8_decode_utf8;

            printablestring_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for super::super::PrintableStringFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            broadcast use vstd::utf8::decode_utf8_encode_utf8;

            printablestring_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for super::super::PrintableStringFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            printablestring_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i> Parser<&'i [u8]> for super::PrintableStringFmt {
    type PT = PrintableString<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if !is_valid_printable_string(bytes) {
            Err(ParseError::custom("Invalid PrintableString"))
        } else if !is_valid_utf8(bytes) {
            Err(ParseError::custom("Invalid UTF-8"))
        } else {
            let inner = utf8_from_bytes_unchecked(bytes);
            Ok((n, PrintableString::new(inner)))
        }
    }
}

impl<Output: OutputBuf, 'i> Serializer<Output, PrintableString<'i>> for super::PrintableStringFmt {
    fn serialize_into(&self, v: &PrintableString<'i>, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.serialize_into(&bytes, obuf);
    }
}

impl<'i> Prepare<PrintableString<'i>> for super::PrintableStringFmt {
    fn prepare(&self, v: &PrintableString<'i>) -> Result<usize, PreSerializeError> {
        broadcast use vstd::utf8::encode_utf8_valid_utf8;

        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.prepare(&bytes)
    }
}

impl<'i> ByteLen<PrintableString<'i>> for super::PrintableStringFmt {
    fn length(&self, v: &PrintableString<'i>) -> usize {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_bytes();
        Tail.length(&bytes)
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf> Serializer<Output, PrintableStringOwned> for super::PrintableStringFmt {
    fn serialize_into(&self, v: &PrintableStringOwned, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_str().as_bytes();
        Tail.serialize_into(&bytes, obuf);
    }
}

#[cfg(feature = "alloc")]
impl Prepare<PrintableStringOwned> for super::PrintableStringFmt {
    fn prepare(&self, v: &PrintableStringOwned) -> Result<usize, PreSerializeError> {
        broadcast use vstd::utf8::encode_utf8_valid_utf8;

        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_str().as_bytes();
        Tail.prepare(&bytes)
    }
}

#[cfg(feature = "alloc")]
impl ByteLen<PrintableStringOwned> for super::PrintableStringFmt {
    fn length(&self, v: &PrintableStringOwned) -> usize {
        proof {
            use_type_invariant(v);
        }
        let bytes = v.inner.as_str().as_bytes();
        Tail.length(&bytes)
    }
}

} // verus!
