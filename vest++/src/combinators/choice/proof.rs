use crate::combinators::Either;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip, B: SPRoundTrip> SPRoundTrip for super::Choice<A, B> {
    proof fn theorem_serialize_parse_roundtrip_internal(&self, v: Self::T, obuf: Seq<u8>) {
        if v.wf() {
            match v {
                Either::Left(va) => {
                    self.0.theorem_serialize_parse_roundtrip_internal(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.theorem_serialize_parse_roundtrip_internal(vb, obuf);
                },
            }
        }
    }
}

impl<A: PSRoundTrip, B: PSRoundTrip> PSRoundTrip for super::Choice<A, B> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(ibuf);
        self.1.theorem_parse_serialize_roundtrip(ibuf);
    }
}

impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Choice<A, B> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
        self.1.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A, B> SpecSerializers for super::Choice<A, B> where A: SpecSerializers, B: SpecSerializers {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        match v {
            Either::Left(va) => {
                self.0.lemma_serialize_equiv(va, obuf);
            },
            Either::Right(vb) => {
                self.1.lemma_serialize_equiv(vb, obuf);
            },
        }
    }
}

} // verus!
