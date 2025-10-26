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
    type Type = SpecPrintableStringValue;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
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
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
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
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PrintableString {
    type Type = PrintableStringValue<'a>;
    type SType = <UTF8String as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    fn length(&self, v: Self::SType) -> usize {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.length(v)
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        Refined {
            inner: UTF8String,
            predicate: PrintableStringPred,
        }.parse(s)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
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

impl SpecPred<Seq<char>> for PrintableStringPred {
    closed spec fn spec_apply(&self, s: &Seq<char>) -> bool {
        forall |i| 0 <= i < s.len() ==> #[trigger] Self::wf_char(s[i])
    }
}

impl Pred<&str> for PrintableStringPred {
    fn apply(&self, s: &&str) -> (res: bool)
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
