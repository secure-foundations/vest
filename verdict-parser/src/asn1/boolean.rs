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
    type Type = bool;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if s.len() < 2 {
            None
        } else if s[0] == 0x01 && s[1] == 0xff {
            Some((2, true))
        } else if s[0] == 0x01 && s[1] == 0x00 {
            Some((2, false))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        if v {
            seq![ 0x01, 0xff ]
        } else {
            seq![ 0x01, 0x00 ]
        }
    }
}

impl SecureSpecCombinator for Boolean {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(buf) {
            assert(self.spec_serialize(v) =~= buf.subrange(0, 2));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Boolean {
    type Type = bool;
    type SType = bool;

    fn length(&self, _v: Self::SType) -> usize {
        2
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
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
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
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

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@)));

        Ok(2)
    }
}

}
