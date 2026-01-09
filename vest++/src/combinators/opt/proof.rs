use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{GoodParser, SpecCombinator, SpecParser, SpecSerializer, SpecType},
};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip> SPRoundTrip for super::Opt<A> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize_dps(v, obuf) == obuf);
                if let Some((n, v)) = self.spec_parse(obuf) {
                    assert(n == 0);
                    assert(v == Option::<A::Type>::None);
                }
            },
            Some(vv) => {
                if self.wf(v) {
                    self.0.theorem_serialize_parse_roundtrip(vv, obuf);
                }
            },
        }
    }
}

impl<A: PSRoundTrip> PSRoundTrip for super::Opt<A> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n, v)) = self.spec_parse(ibuf) {
            match v {
                None => {
                    assert(n == 0);
                    assert(self.spec_serialize_dps(v, obuf) == obuf);
                },
                Some(vv) => {
                    self.0.theorem_parse_serialize_roundtrip(ibuf, obuf);
                },
            }
        }
    }
}

impl<A: NonMalleable> NonMalleable for super::Opt<A> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A> Deterministic for super::Opt<A> where A: Deterministic + SpecParser {
    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {},
            Some(vv) => {
                if self.wf(v) {
                    self.0.lemma_serialize_equiv(vv, obuf);
                }
            },
        }
    }
}

} // verus!
