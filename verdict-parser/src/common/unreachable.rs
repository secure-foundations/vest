use super::*;
use vstd::prelude::*;

verus! {

/// Similar to Fail, but without error message
#[derive(View)]
pub struct Unreachable;

impl SpecCombinator for Unreachable {
    type Type = ();

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        None
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        seq![]
    }
}

impl SecureSpecCombinator for Unreachable {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Unreachable {
    type Type = ();
    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    #[inline(always)]
    fn parse(&self, _s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        Err(ParseError::Other("Unreachable".to_string()))
    }

    #[inline(always)]
    fn serialize(&self, _v: Self::SType, _data: &mut Vec<u8>, _pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        Err(SerializeError::Other("Unreachable".to_string()))
    }
}

// Unreachable is disjoint from any other combinator
impl<T> DisjointFrom<T> for Unreachable where T: SpecCombinator {
    open spec fn disjoint_from(&self, c: &T) -> bool {
        true
    }

    proof fn parse_disjoint_on(&self, c: &T, buf: Seq<u8>) {
    }
}

} // verus!
