use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that succeeds only at the end of the input buffer and consumes nothing
pub struct End;

impl View for End {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for End {
    type Type = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if s.len() == 0 {
            Some((0, ()))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        Seq::empty()
    }
}

impl SecureSpecCombinator for End {
    open spec fn is_prefix_secure() -> bool {
        false
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<'x, I, O> for End {
    type Type = ();

    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if s.len() == 0 {
            Ok((0, ()))
        } else {
            Err(ParseError::NotEof)
        }
    }

    fn serialize(&self, _v: Self::SType, _data: &mut O, _pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        assert(seq_splice(_data@, _pos, Seq::<u8>::empty()) == _data@);
        Ok(0)
    }
}

} // verus!
