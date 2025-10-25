use super::*;
use vstd::prelude::*;

verus! {

/// Combainator for BOOLEAN in ASN.1
/// TRUE = 0x01 0x01 0xff
/// FALSE = 0x01 0x01 0x00
#[derive(Debug, View)]
pub struct Boolean;

asn1_tagged!(Boolean, tag_of!(BOOLEAN));

impl SpecCombinator for Boolean {
    type SpecResult = bool;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if s.len() < 2 {
            Err(())
        } else if s[0] == 0x01 && s[1] == 0xff {
            Ok((2, true))
        } else if s[0] == 0x01 && s[1] == 0x00 {
            Ok((2, false))
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v {
            Ok(seq![ 0x01, 0xff ])
        } else {
            Ok(seq![ 0x01, 0x00 ])
        }
    }
}

impl SecureSpecCombinator for Boolean {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.spec_parse(buf) {
            assert(self.spec_serialize(v).unwrap() =~= buf.subrange(0, 2));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl Combinator for Boolean {
    type Result<'a> = bool;
    type Owned = bool;

    closed spec fn spec_length(&self) -> Option<usize> {
        Some(2)
    }

    fn length(&self) -> Option<usize> {
        Some(2)
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if s.len() < 2 {
            Err(ParseError::UnexpectedEndOfInput)
        } else if s[0] == 0x01 && s[1] == 0xff {
            Ok((2, true))
        } else if s[0] == 0x01 && s[1] == 0x00 {
            Ok((2, false))
        } else {
            Err(ParseError::Other("Invalid boolean value".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        if pos > usize::MAX - 2 || pos + 2 > data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }

        if v {
            data.set(pos, 0x01);
            data.set(pos + 1, 0xff);
        } else {
            data.set(pos, 0x01);
            data.set(pos + 1, 0x00);
        }

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));

        Ok(2)
    }
}

}
