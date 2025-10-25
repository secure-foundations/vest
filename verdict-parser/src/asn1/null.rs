use super::*;
use vstd::prelude::*;

verus! {

/// Combainator for NULL in ASN.1
/// NULL = 05 00 (with tag)
#[derive(Debug, View)]
pub struct Null;

#[derive(Debug, View, PolyfillClone)]
pub struct NullValue;

asn1_tagged!(Null, tag_of!(NULL));

impl SpecCombinator for Null {
    type Type = NullValue;
    
    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }
    
    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, NullValue)> {
        if s.len() >= 1 && s[0] == 0x00 {
            Some((1, NullValue))
        } else {
            None
        }
    }

    spec fn spec_serialize(&self, v: NullValue) -> Seq<u8> {
        seq![ 0x00 ]
    }
}

impl SecureSpecCombinator for Null {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    spec fn is_productive() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: NullValue) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(buf) {
            assert(self.spec_serialize(v) =~= buf.subrange(0, 1));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Null {
    type Type = NullValue;
    type SType = NullValue;

    fn length(&self, _v: Self::SType) -> usize {
        1
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if s.len() >= 1 && s[0] == 0x00 {
            Ok((1, NullValue))
        } else {
            Err(ParseError::Other("Invalid null value".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, _v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        if pos > usize::MAX - 1 || pos + 1 > data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }
        data.set(pos, 0x00);
        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(_v@)));
        Ok(1)
    }
}

}
