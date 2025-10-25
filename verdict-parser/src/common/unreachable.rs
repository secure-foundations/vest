use super::*;
use vstd::prelude::*;

verus! {

/// Similar to Fail, but without error message
#[derive(View)]
pub struct Unreachable;

impl SpecCombinator for Unreachable {
    type SpecResult = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        Err(())
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        Err(())
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
    }
}

impl SecureSpecCombinator for Unreachable {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }
}

impl Combinator for Unreachable {
    type Result<'a> = ();

    type Owned = ();

    open spec fn spec_length(&self) -> Option<usize> {
        Some(0)
    }

    fn length(&self) -> Option<usize> {
        Some(0)
    }

    #[inline(always)]
    fn parse<'a>(&self, _s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        Err(ParseError::Other("Unreachable".to_string()))
    }

    #[inline(always)]
    fn serialize(&self, _v: Self::Result<'_>, _data: &mut Vec<u8>, _pos: usize) -> (res: Result<
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
