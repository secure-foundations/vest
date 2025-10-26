use super::*;
use vstd::prelude::*;

verus! {

/// A combinator that only matches the end of the buffer
#[derive(Debug, View)]
pub struct End;

#[derive(Debug, View, PolyfillClone, Eq, PartialEq)]
pub struct EndValue;

impl SpecCombinator for End {
    type Type = EndValue;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if s.len() == 0 {
            Some((0, EndValue))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        seq![]
    }
}

impl SecureSpecCombinator for End {
    open spec fn is_prefix_secure() -> bool {
        false
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        let empty: Seq<u8> = seq![];
        assert(buf.subrange(0, 0) == empty);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for End {
    type Type = EndValue;
    type SType = EndValue;

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if s.len() == 0 {
            Ok((0, EndValue))
        } else {
            Err(ParseError::Other("Expecting end of the buffer".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, _v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        if pos <= data.len() {
            let ghost empty: Seq<u8> = seq![];
            assert(data@ =~= seq_splice(old(data)@, pos, empty));
            Ok(0)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

}
