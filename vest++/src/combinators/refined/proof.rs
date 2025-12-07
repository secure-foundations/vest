use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip, Serializable},
    spec::SpecCombinator,
};
use vstd::prelude::*;

verus! {

impl<A: SpecCombinator> SPRoundTrip for super::Refined<A> where A: SPRoundTrip {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip(v, obuf);
    }
}

impl<A: SpecCombinator> Serializable for super::Refined<A> where A: Serializable {
    proof fn lemma_parse_serializable(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.inner.lemma_parse_serializable(ibuf);
            let obuf = choose|obuf: Seq<u8>| self.inner.serializable(v, obuf);
            assert(self.serializable(v, obuf));
        }
    }
}

impl<A: PSRoundTrip> PSRoundTrip for super::Refined<A> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

impl<A: NonMalleable> NonMalleable for super::Refined<A> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

} // verus!
