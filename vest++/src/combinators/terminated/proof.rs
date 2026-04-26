use super::spec::terminated;
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
    open spec fn unambiguous(&self) -> bool {
        Pair(self.0, self.1).unambiguous()
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
    A: SoundParser + NonMalleable,
    B: SoundParser + NonMalleable + AdmitsUniqueVal,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& Pair(self.0, self.1).nonmal_inv()
        &&& Pair(self.0, self.1).sound_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let pair = Pair(self.0, self.1);
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    assert(pair.spec_parse(buf1) matches Some((_, _)));
                    assert(pair.spec_parse(buf2) matches Some((_, _)));
                    let (_m1, p1) = pair.spec_parse(buf1)->0;
                    let (_m2, p2) = pair.spec_parse(buf2)->0;
                    assert(p1.0 == v1);
                    assert(p2.0 == v2);
                    pair.lemma_parse_sound_value(buf1);
                    pair.lemma_parse_sound_value(buf2);
                    self.1.lemma_unique_consistent_val(p1.1, p2.1);
                    assert(p1 == p2);
                    pair.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
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

impl<A, B, BVal, const NONMAL: bool> SPRoundTripDps for super::Terminated2<
    A,
    B,
    BVal,
    NONMAL,
> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
    BVal: DeepView<V = B::SValue>,
{
    open spec fn unambiguous(&self) -> bool {
        Pair(self.a, self.b).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<A, B, BVal> NonMalleable for super::Terminated2<A, B, BVal, true> where
    A: SoundParser + NonMalleable,
    B: SoundParser + NonMalleable,
    BVal: DeepView<V = B::PVal>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& Pair(self.a, self.b).sound_inv()
        &&& Pair(self.a, self.b).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, true>(self.a, self.b, self.b_val.deep_view());
        fmt.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A, B, BVal, const NONMAL: bool> NoLookAhead for super::Terminated2<A, B, BVal, NONMAL> where
    A: NoLookAhead,
    B: NoLookAhead,
    BVal: DeepView<V = B::PVal>,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.lemma_no_lookahead(i1, i2);
    }
}

impl<A, B, BVal, const NONMAL: bool> EquivSerializersGeneral for super::Terminated2<
    A,
    B,
    BVal,
    NONMAL,
> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral + Consistency<Val = B::SVal>,
    BVal: DeepView<V = B::SValue>,
{
    open spec fn equiv_general_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.lemma_serialize_equiv(v, obuf);
    }
}

impl<A, B, BVal, const NONMAL: bool> EquivSerializers for super::Terminated2<
    A,
    B,
    BVal,
    NONMAL,
> where
    A: EquivSerializersGeneral,
    B: EquivSerializers + Consistency<Val = B::SVal>,
    BVal: DeepView<V = B::SValue>,
{
    open spec fn equiv_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let fmt = terminated::<_, _, _, _, NONMAL>(self.a, self.b, self.b_val.deep_view());
        fmt.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
