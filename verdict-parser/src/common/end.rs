use super::*;
use vstd::prelude::*;

verus! {

/// A combinator that only matches the end of the buffer
#[derive(Debug, View)]
pub struct End;

#[derive(Debug, View, PolyfillClone, Eq, PartialEq)]
pub struct EndValue;

impl SpecCombinator for End {
    type SpecResult = EndValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if s.len() == 0 {
            Ok((0, EndValue))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        Ok(seq![])
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}
}

impl SecureSpecCombinator for End {
    open spec fn is_prefix_secure() -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        let empty: Seq<u8> = seq![];
        assert(buf.subrange(0, 0) == empty);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl Combinator for End {
    type Result<'a> = EndValue;
    type Owned = EndValue;

    closed spec fn spec_length(&self) -> Option<usize> {
        Some(0)
    }

    fn length(&self) -> Option<usize> {
        Some(0)
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if s.len() == 0 {
            Ok((0, EndValue))
        } else {
            Err(ParseError::Other("Expecting end of the buffer".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, _v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
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
