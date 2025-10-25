use super::*;
/// TODO: maybe refactor this using Refined
use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

verus! {

/// Combinator for IA5String in ASN.1
/// Essentially a wrapper around Octet
/// that checks that each byte is <= 127
#[derive(Debug, View)]
pub struct IA5String;

asn1_tagged!(IA5String, tag_of!(IA5_STRING));

pub type SpecIA5StringValue = Seq<char>;
pub type IA5StringValue<'a> = &'a str;
pub type IA5StringValueOwned = String;

impl SpecCombinator for IA5String {
    type Type = SpecIA5StringValue;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.spec_parse(s)
    }

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.spec_serialize(v)
    }
}

impl SecureSpecCombinator for IA5String {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    spec fn is_productive() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.lemma_prefix_secure(s1, s2);
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IA5String {
    type Type = IA5StringValue<'a>;
    type SType = IA5StringValueOwned;

    fn length(&self, v: Self::SType) -> usize {
        v.len()
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.parse(s)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        Refined {
            inner: UTF8String,
            predicate: IA5StringPred,
        }.serialize(v, data, pos)
    }
}

/// A condition that the minimal encoding is used
#[derive(View)]
pub struct IA5StringPred;

impl IA5StringPred {
    closed spec fn wf_char(c: char) -> bool {
        c <= '\x7f'
    }

    #[inline(always)]
    fn exec_wf_char(c: char) -> (res: bool)
        ensures res == Self::wf_char(c)
    {
        c <= '\x7f'
    }
}

impl SpecPred for IA5StringPred {
    closed spec fn spec_apply(&self, s: &Seq<char>) -> bool {
        forall |i| 0 <= i < s.len() ==> #[trigger] Self::wf_char(s[i])
    }
}

impl Pred for IA5StringPred {
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

#[cfg(test)]
mod tests {
    use super::*;
    use der::Encode;

    fn serialize_ia5_string(v: &str) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; v.len() + 10];
        data[0] = 0x16; // Prepend the tag byte
        let len = IA5String.serialize(v, &mut data, 1)?;
        data.truncate(len + 1);
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        let diff = |s: &str| {
            let res1 = serialize_ia5_string(s).map_err(|_| ());
            let res2 = der::asn1::Ia5StringRef::new(s)
                .unwrap()
                .to_der()
                .map_err(|_| ());
            assert_eq!(res1, res2);
        };

        diff("");
        diff("\x7f");
        diff("asdsad");
        diff("aaaaaa");
        diff("aaaaa".repeat(100).as_str());
    }
}
