use crate::combinators::Either;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTripDps, B: SPRoundTripDps> SPRoundTripDps for super::Choice<A, B> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        if v.wf() {
            match v {
                Either::Left(va) => {
                    self.0.theorem_serialize_dps_parse_roundtrip(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.theorem_serialize_dps_parse_roundtrip(vb, obuf);
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

impl<A, B> EquivSerializersGeneral for super::Choice<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
 {
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

impl<A, B> EquivSerializers for super::Choice<A, B> where A: EquivSerializers, B: EquivSerializers {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        match v {
            Either::Left(va) => {
                self.0.lemma_serialize_equiv_on_empty(va);
            },
            Either::Right(vb) => {
                self.1.lemma_serialize_equiv_on_empty(vb);
            },
        }
    }
}

} // verus!
