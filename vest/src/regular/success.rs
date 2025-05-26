use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that always succeeds and consumes nothing
pub struct Success;

impl View for Success {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for Success {
    type Type = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        Some((0, ()))
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        Seq::empty()
    }
}

impl SecureSpecCombinator for Success {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        assert(s.subrange(0, 0) == Seq::<u8>::empty());
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<'x, I, O> for Success {
    type Type = ();

    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    fn parse(&self, _s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        Ok((0, ()))
    }

    fn serialize(&self, _v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        assert(seq_splice(data@, pos, Seq::<u8>::empty()) == data@);
        Ok(0)
    }
}

} // verus!
