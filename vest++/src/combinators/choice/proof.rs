use super::spec::triv;
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

// impl<A: PSRoundTrip, B: PSRoundTrip> PSRoundTrip for super::Choice<A, B> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.0.theorem_parse_serialize_roundtrip(ibuf);
//         self.1.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
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


impl<A: SPRoundTripDps, B: SPRoundTripDps<T = A::T>> SPRoundTripDps for super::Alt<A, B> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        if v.wf() {
            let b = choose|flip: bool| triv(flip);
            if b {
                self.0.theorem_serialize_dps_parse_roundtrip(v, obuf);
            } else {
                self.1.theorem_serialize_dps_parse_roundtrip(v, obuf);
            }
        }
    }
}

// NonMalleable only holds for [`Alt`] when the two parsers produce disjoint sets of values.
// This ensures that if two byte sequences parse to the same value, they must have used the same underlying parser.
impl<A, B> NonMalleable for super::Alt<A, B> where
    A: NonMalleable + DisjointRanges<B>,
    B: NonMalleable<PVal = A::PVal>,
{
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let a_parses_buf1 = self.0.spec_parse(buf1) is Some;
                    let a_parses_buf2 = self.0.spec_parse(buf2) is Some;
                    if a_parses_buf1 && a_parses_buf2 {
                        // Both use parser A
                        self.0.lemma_parse_non_malleable(buf1, buf2);
                    } else if !a_parses_buf1 && !a_parses_buf2 {
                        // Both use parser B
                        self.1.lemma_parse_non_malleable(buf1, buf2);
                    } else {
                        // One uses A, one uses B - this contradicts DisjointRanges
                        self.0.lemma_disjoint_ranges(&self.1, buf1, buf2);
                        assert(v1 != v2);
                    }
                }
            }
        }
    }
}



impl<A, B> EquivSerializersGeneral for super::Alt<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral<SVal = A::SVal>,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.lemma_serialize_equiv(v, obuf);
        } else {
            self.1.lemma_serialize_equiv(v, obuf);
        }
    }
}

impl<A, B> EquivSerializers for super::Alt<A, B> where A: EquivSerializers, B: EquivSerializers<SVal = A::SVal> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.lemma_serialize_equiv_on_empty(v);
        } else {
            self.1.lemma_serialize_equiv_on_empty(v);
        }
    }
}



} // verus!
