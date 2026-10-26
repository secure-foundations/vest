//! Correctness proofs for tail-position formats.
use crate::combinators::Pair;
use crate::{
    combinators::{Optional, Repeat},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl SPRoundTripDps for super::Tail {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
    }
}

impl NonMalleable for super::Tail {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl Productive for super::Tail {
    open spec fn productive_inv(&self) -> bool {
        false
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
    }
}

impl EquivSerializers for super::Tail {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl SPRoundTripDps for super::Eof {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
    }
}

impl NonMalleable for super::Eof {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl Productive for super::Eof {
    open spec fn productive_inv(&self) -> bool {
        false
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
    }
}

impl EquivSerializers for super::Eof {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl<A, B> SPRoundTripDps for super::PairRev<A, B> where
    A: SPRoundTripDps + NonTailFmt + NoLookAhead,
    B: StaticByteLen + EquivSerializers + GoodSerializer + SPRoundTrip,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.0.equiv_inv()
        &&& self.0.sp_roundtrip_inv()
        &&& self.1.unambiguous()
        &&& self.1.serialize_dps_inv()
        &&& self.1.safe_inv()
        &&& self.1.no_lookahead_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        broadcast use vstd::seq_lib::group_seq_properties;

        let serialized1 = self.0.spec_serialize_dps(v.1, seq![]);
        let serialized0 = self.1.spec_serialize_dps(v.0, serialized1);
        let n1 = self.1.byte_len(v.0) as int;
        let n2 = self.0.byte_len(v.1) as int;

        self.0.lemma_serialize_equiv_on_empty(v.1);
        self.0.lemma_serialize_len(v.1);
        self.0.theorem_serialize_parse_roundtrip(v.1);
        self.0.lemma_static_len_matches_byte_len(v.1);

        self.1.theorem_serialize_dps_parse_roundtrip(v.0, serialized1);
        self.1.lemma_serialize_dps_prepend(v.0, serialized1);
        self.1.lemma_serialize_dps_len(v.0, serialized1);
        assert(serialized0[0..n1][0..n1] == serialized0[0..n1]);
        self.1.lemma_no_lookahead(serialized0, serialized0[0..n1]);
        assert(self.1.spec_parse(serialized0[0..n1]) == Some((n1, v.0)));

        assert(self.0.spec_parse(serialized0[n1..]) == Some((n2, v.1)));
        assert(self.spec_parse(serialized0) == Some((n1 + n2, v)));
    }
}

impl<A, B> NonMalleable for super::PairRev<A, B> where
    A: NonMalleable,
    B: StaticByteLen + NonMalleable<PVal = B::T>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.0.nonmal_inv()
        &&& self.1.nonmal_inv()
        &&& self.0.safe_inv()
        &&& self.1.safe_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let prefix1 = buf1.len() - B::static_byte_len();
                    let prefix2 = buf2.len() - B::static_byte_len();
                    self.1.lemma_parse_non_malleable(buf1[0..prefix1], buf2[0..prefix2]);
                    self.0.lemma_parse_non_malleable(buf1[prefix1..], buf2[prefix2..]);

                    let (n1b, b1) = self.0.spec_parse(buf1[prefix1..])->0;
                    let (n2b, b2) = self.0.spec_parse(buf2[prefix2..])->0;
                    let (n1a, a1) = self.1.spec_parse(buf1[0..prefix1])->0;
                    let (n2a, a2) = self.1.spec_parse(buf2[0..prefix2])->0;
                    assert(prefix1 == n1a && prefix2 == n2a);
                    assert(n1 == buf1.len() && n2 == buf2.len());

                    self.0.lemma_parse_safe(buf1[prefix1..]);
                    self.0.lemma_parse_safe(buf2[prefix2..]);
                    self.1.lemma_parse_safe(buf1[0..prefix1]);
                    self.1.lemma_parse_safe(buf2[0..prefix2]);

                    assert(buf1[0..n1] == buf2[0..n2]) by {
                        assert(buf1[0..n1] == buf1[0..n1a] + buf1[n1a..][0..n1b]);
                        assert(buf2[0..n2] == buf2[0..n2a] + buf2[n2a..][0..n2b]);
                        assert(buf1[0..prefix1][0..n1a] == buf1[0..n1a]);
                        assert(buf2[0..prefix2][0..n2a] == buf2[0..n2a]);
                    }
                }
            }
        }
    }
}

impl<A: Productive, B: StaticByteLen + SafeParser<PVal = B::T>> Productive for super::PairRev<
    A,
    B,
> {
    open spec fn productive_inv(&self) -> bool {
        B::static_byte_len() > 0 || (self.1.productive_inv() && self.1.safe_inv())
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
        if let Some((n, _v)) = self.spec_parse(s) {
            let prefix = s.len() - B::static_byte_len();
            let (n1, _a) = self.1.spec_parse(s[0..prefix])->0;
            let (n2, _b) = self.0.spec_parse(s[prefix..])->0;
            assert(n == n1 + n2);
            if B::static_byte_len() > 0 {
                assert(n2 == B::static_byte_len());
                assert(n2 > 0);
            } else {
                self.1.lemma_productive(s[0..prefix]);
                assert(n1 > 0);
            }
            assert(n > 0);
        }
    }
}

impl<A, B> EquivSerializers for super::PairRev<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        Pair(self.1, self.0).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Pair(self.1, self.0).lemma_serialize_equiv_on_empty((v.0, v.1));
    }
}

impl<C: SPRoundTripDps + NonTailFmt + Productive> SPRoundTripDps for super::OptionalEnd<C> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.0.unambiguous()
        &&& self.0.safe_inv()
        &&& self.0.productive_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        broadcast use crate::combinators::disjoint::lemma_disjoint_eof;

        Optional(self.0, super::Eof).theorem_serialize_dps_parse_roundtrip((v, ()), obuf);
    }
}

impl<C: NonMalleable + SafeParser> NonMalleable for super::OptionalEnd<C> {
    open spec fn nonmal_inv(&self) -> bool {
        Optional(self.0, super::Eof).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Optional(self.0, super::Eof).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<C: SafeParser> Productive for super::OptionalEnd<C> {
    open spec fn productive_inv(&self) -> bool {
        false
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
    }
}

impl<C: EquivSerializersGeneral> EquivSerializers for super::OptionalEnd<C> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Optional(self.0, super::Eof).lemma_serialize_equiv_on_empty((v, ()));
    }
}

impl<C: SPRoundTripDps + NonTailFmt + Productive> SPRoundTripDps for super::RepeatTillEnd<C> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.0.unambiguous()
        &&& self.0.safe_inv()
        &&& self.0.productive_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        broadcast use crate::combinators::disjoint::lemma_disjoint_eof;

        Repeat(self.0, super::Eof).theorem_serialize_dps_parse_roundtrip((v, ()), obuf);
    }
}

impl<C: NonMalleable + SafeParser> NonMalleable for super::RepeatTillEnd<C> {
    open spec fn nonmal_inv(&self) -> bool {
        Repeat(self.0, super::Eof).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Repeat(self.0, super::Eof).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<C: SafeParser> Productive for super::RepeatTillEnd<C> {
    open spec fn productive_inv(&self) -> bool {
        false
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
    }
}

impl<C: EquivSerializersGeneral> EquivSerializers for super::RepeatTillEnd<C> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Repeat(self.0, super::Eof).lemma_serialize_equiv_on_empty((v, ()));
    }
}

} // verus!
