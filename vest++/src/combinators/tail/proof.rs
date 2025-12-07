use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::SpecCombinator,
};
use vstd::prelude::*;

verus! {

impl SPRoundTrip for super::Tail {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
    }
}

impl PSRoundTrip for super::Tail {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
    }
}

impl NonMalleable for super::Tail {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

} // verus!
