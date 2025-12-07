use crate::combinators::Either;
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{SpecType, SpecParser, SpecSerializer, SpecCombinator},
};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip, B: SPRoundTrip> SPRoundTrip for super::Choice<A, B> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            match v {
                Either::Left(va) => {
                    self.0.theorem_serialize_parse_roundtrip(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.theorem_serialize_parse_roundtrip(vb, obuf);
                },
            }
        }
    }
}

impl<A: PSRoundTrip, B: PSRoundTrip> PSRoundTrip for super::Choice<A, B> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(ibuf, obuf);
        self.1.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Choice<A, B> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
        self.1.lemma_parse_non_malleable(buf1, buf2);
    }
}

} // verus!
