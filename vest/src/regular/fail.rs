use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator used for custom error message
pub struct Fail(pub String);

impl View for Fail {
    type V = Fail;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for Fail {
    type Type = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        Err(())
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        Err(())
    }
}

impl SecureSpecCombinator for Fail {
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
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I: VestInput, O: VestOutput<I>> Combinator<I, O> for Fail {
    type Type = ();

    open spec fn spec_length(&self) -> Option<usize> {
        Some(0)
    }

    fn length(&self) -> Option<usize> {
        Some(0)
    }

    fn parse(&self, _s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        Err(ParseError::Other(self.0.clone()))
    }

    fn serialize(&self, _v: Self::Type, _data: &mut O, _pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        Err(SerializeError::Other(self.0.clone()))
    }
}

} // verus!
