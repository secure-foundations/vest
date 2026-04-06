use crate::{
    combinators::Pair,
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTripDps for super::Terminated<A, B> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        Pair(self.0, self.1).sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let vb = choose|vb: B::T| self.1.consistent(vb);
        let pair = Pair(self.0, self.1);
        assert(pair.consistent((v, vb)));
        pair.theorem_serialize_dps_parse_roundtrip((v, vb), obuf);
        assert(self.byte_len(v) == pair.byte_len((v, vb)));
    }
}

impl<A, B> NonMalleable for super::Terminated<A, B> where
    A: NonMalleable,
    B: NonMalleable + AdmitsUniqueVal,
 {
    open spec fn nonmal_inv(&self) -> bool {
        Pair(self.0, self.1).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        super::terminated_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).lemma_parse_non_malleable(
            buf1,
            buf2,
        );
    }
}

impl<A, B> NoLookAhead for super::Terminated<A, B> where
    A: NoLookAhead,
    B: NoLookAhead + AdmitsUniqueVal,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        Pair(self.0, self.1).no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let pair = Pair(self.0, self.1);
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(pair.spec_parse(i1) matches Some((_, _)));
                    let (_m, p) = pair.spec_parse(i1)->0;
                    assert(p.0 == v);
                    pair.lemma_no_lookahead(i1, i2);
                    assert(self.spec_parse(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl<A, B> EquivSerializersGeneral for super::Terminated<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral + Consistency<Val = B::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        Pair(self.0, self.1).equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let vb = choose|vb: B::SVal| self.1.consistent(vb);
        Pair(self.0, self.1).lemma_serialize_equiv((v, vb), obuf);
    }
}

impl<A, B> EquivSerializers for super::Terminated<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializers + Consistency<Val = B::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        Pair(self.0, self.1).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let vb = choose|vb: B::SVal| self.1.consistent(vb);
        Pair(self.0, self.1).lemma_serialize_equiv_on_empty((v, vb));
    }
}

} // verus!
