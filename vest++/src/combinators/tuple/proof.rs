use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTripDps + NonTailFmt, B: SPRoundTripDps> SPRoundTripDps for super::Pair<A, B> {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        &&& self.0.sp_roundtrip_dps_inv()
        &&& self.1.sp_roundtrip_dps_inv()
        &&& self.0.serialize_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        let serialized0 = self.0.spec_serialize_dps(v.0, serialized1);
        self.1.theorem_serialize_dps_parse_roundtrip(v.1, obuf);
        self.0.theorem_serialize_dps_parse_roundtrip(v.0, serialized1);
        self.0.lemma_serialize_dps_prepend(v.0, serialized1);
        self.0.lemma_serialize_dps_len(v.0, serialized1);
        if let Some((n0, v0)) = self.0.spec_parse(serialized0) {
            assert(n0 == serialized0.len() - serialized1.len());
            assert(serialized0.skip(n0) == serialized1);
        }
    }
}

// impl<A: PSRoundTrip + GoodSerializerDps + EquivSerializersGeneral, B: PSRoundTrip> PSRoundTrip for (
//     A,
//     B,
// ) {
// }
impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Pair<A, B> {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.0.nonmal_inv()
        &&& self.1.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (n1a, _) = self.0.spec_parse(buf1)->0;
                    let (n2a, _) = self.0.spec_parse(buf2)->0;
                    let (n1b, _) = self.1.spec_parse(buf1.skip(n1a))->0;
                    let (n2b, _) = self.1.spec_parse(buf2.skip(n2a))->0;
                    self.0.lemma_parse_safe(buf1);
                    self.0.lemma_parse_safe(buf2);
                    self.1.lemma_parse_safe(buf1.skip(n1a));
                    self.1.lemma_parse_safe(buf2.skip(n2a));
                    self.0.lemma_parse_non_malleable(buf1, buf2);
                    self.1.lemma_parse_non_malleable(buf1.skip(n1a), buf2.skip(n2a));
                    assert(n1 == n1a + n1b && n2 == n2a + n2b);
                    assert(buf1.take(n1) == buf2.take(n2)) by {
                        assert(buf1.take(n1) == buf1.take(n1a) + buf1.skip(n1a).take(n1b));
                        assert(buf2.take(n2) == buf2.take(n2a) + buf2.skip(n2a).take(n2b));
                    }
                }
            }
        }
    }
}

pub(crate) proof fn lemma_take_skip<T>(s: Seq<T>, n1: int, n2: int)
    requires
        0 <= n1,
        0 <= n2,
        n1 + n2 <= s.len(),
    ensures
        s.take(n1 + n2).skip(n1) == s.skip(n1).take(n2),
{
}

impl<A: NoLookAhead, B: NoLookAhead> NoLookAhead for super::Pair<A, B> {
    open spec fn no_lookahead_inv(&self) -> bool {
        &&& self.0.no_lookahead_inv()
        &&& self.1.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        broadcast use vstd::seq_lib::group_seq_properties;

        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    if let Some((n1, v1)) = self.0.spec_parse(i1) {
                        if let Some((n2, v2)) = self.1.spec_parse(i1.skip(n1)) {
                            self.lemma_parse_safe(i1);
                            self.0.lemma_parse_safe(i1);
                            self.1.lemma_parse_safe(i1.skip(n1));
                            assert(self.no_lookahead_inv());
                            assert(self.0.no_lookahead_inv());
                            assert(self.1.no_lookahead_inv());
                            assert(i2.take(n1) == i1.take(n1));
                            self.0.lemma_no_lookahead(i1, i2);
                            assert(i2.skip(n1).take(n2) == i1.skip(n1).take(n2)) by {
                                lemma_take_skip(i1, n1, n2);
                                lemma_take_skip(i2, n1, n2);
                            };
                            self.1.lemma_no_lookahead(i1.skip(n1), i2.skip(n1));
                        }
                    }
                }
            }
        }
    }
}

impl<A, B> EquivSerializersGeneral for super::Pair<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let obuf1 = self.1.spec_serialize_dps(v.1, obuf);

        self.1.lemma_serialize_equiv(v.1, obuf);
        self.0.lemma_serialize_equiv(v.0, obuf1);

        // From self.1.lemma_serialize_equiv:
        // self.1.spec_serialize_dps(v.1, obuf) == self.1.spec_serialize(v.1) + obuf
        // So: obuf1 == self.1.spec_serialize(v.1) + obuf

        // From self.0.lemma_serialize_equiv:
        // self.0.spec_serialize_dps(v.0, obuf1) == self.0.spec_serialize(v.0) + obuf1

        // Therefore:
        // spec_serialize_dps(v, obuf) = self.0.spec_serialize_dps(v.0, obuf1)
        //                              = self.0.spec_serialize(v.0) + obuf1
        //                              = self.0.spec_serialize(v.0) + self.1.spec_serialize(v.1) + obuf
        //                              = spec_serialize(v) + obuf
    }
}

impl<A, B> EquivSerializers for super::Pair<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let empty = Seq::empty();
        let obuf = self.1.spec_serialize_dps(v.1, empty);
        self.1.lemma_serialize_equiv_on_empty(v.1);
        self.0.lemma_serialize_equiv(v.0, obuf);
    }
}

} // verus!
