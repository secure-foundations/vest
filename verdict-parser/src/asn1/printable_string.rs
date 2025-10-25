use super::*;
/// TODO: maybe refactor this using Refined
use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

verus! {

/// Combinator for PrintableString in ASN.1
/// Essentially a wrapper around Octet
/// that checks that each byte is <= 127
#[derive(Debug, View)]
pub struct PrintableString;

asn1_tagged!(PrintableString, tag_of!(PRINTABLE_STRING));

pub type SpecPrintableStringValue = Seq<char>;
pub type PrintableStringValue<'a> = &'a str;
pub type PrintableStringValueOwned = String;

impl SpecCombinator for PrintableString {
    type SpecResult = SpecPrintableStringValue;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.spec_serialize(v)
    }
}

impl SecureSpecCombinator for PrintableString {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for PrintableString {
    type Result<'a> = PrintableStringValue<'a>;
    type Owned = PrintableStringValueOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.parse(s)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.serialize(v, data, pos)
    }
}

/// A condition that the minimal encoding is used
#[derive(View)]
pub struct PrintableStringPred;

impl PrintableStringPred {
    closed spec fn wf_char(c: char) -> bool {
        // https://en.wikipedia.org/wiki/PrintableString
        ||| ('A' <= c && c <= 'Z')
        ||| ('a' <= c && c <= 'z')
        ||| ('0' <= c && c <= '9')
        ||| c == ' '
        ||| ('\'' <= c && c <= ')')
        ||| ('+' <= c && c <= '/')
        ||| c == ':'
        ||| c == '='
        ||| c == '?'
    }

    #[inline(always)]
    fn exec_wf_char(c: char) -> (res: bool)
        ensures res == Self::wf_char(c)
    {
        ('A' <= c && c <= 'Z') ||
        ('a' <= c && c <= 'z') ||
        ('0' <= c && c <= '9') ||
        c == ' ' ||
        ('\'' <= c && c <= ')') ||
        ('+' <= c && c <= '/') ||
        c == ':' ||
        c == '=' ||
        c == '?'
    }
}

impl SpecPred for PrintableStringPred {
    type Input = Seq<char>;

    closed spec fn spec_apply(&self, s: &Self::Input) -> bool {
        forall |i| 0 <= i < s.len() ==> #[trigger] Self::wf_char(s[i])
    }
}

impl Pred for PrintableStringPred {
    type Input<'a> = &'a str;
    type InputOwned = String;

    fn apply(&self, s: &Self::Input<'_>) -> (res: bool)
    {
        let len = s.unicode_len();
        for i in 0..len
            invariant
                len == s@.len(),
                forall |j| 0 <= j < i ==> #[trigger] Self::wf_char(s@[j]),
        {
            if !Self::exec_wf_char(s.get_char(i)) {
                return false;
            }
        }
        return true;
    }
}

}
