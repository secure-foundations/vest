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

// impl PSRoundTrip for super::Tail {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//     }
// }
impl NonMalleable for super::Tail {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
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

// impl PSRoundTrip for super::Eof {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//     }
// }
impl NonMalleable for super::Eof {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
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
        assert(serialized0.take(n1).take(n1) == serialized0.take(n1));
        self.1.lemma_no_lookahead(serialized0, serialized0.take(n1));
        assert(self.1.spec_parse(serialized0.take(n1)) == Some((n1, v.0)));

        assert(self.0.spec_parse(serialized0.skip(n1)) == Some((n2, v.1)));
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
                    self.1.lemma_parse_non_malleable(buf1.take(prefix1), buf2.take(prefix2));
                    self.0.lemma_parse_non_malleable(buf1.skip(prefix1), buf2.skip(prefix2));

                    let (n1b, b1) = self.0.spec_parse(buf1.skip(prefix1))->0;
                    let (n2b, b2) = self.0.spec_parse(buf2.skip(prefix2))->0;
                    let (n1a, a1) = self.1.spec_parse(buf1.take(prefix1))->0;
                    let (n2a, a2) = self.1.spec_parse(buf2.take(prefix2))->0;
                    assert(prefix1 == n1a && prefix2 == n2a);
                    assert(n1 == buf1.len() && n2 == buf2.len());

                    self.0.lemma_parse_safe(buf1.skip(prefix1));
                    self.0.lemma_parse_safe(buf2.skip(prefix2));
                    self.1.lemma_parse_safe(buf1.take(prefix1));
                    self.1.lemma_parse_safe(buf2.take(prefix2));

                    assert(buf1.take(n1) == buf2.take(n2)) by {
                        assert(buf1.take(n1) == buf1.take(n1a) + buf1.skip(n1a).take(n1b));
                        assert(buf2.take(n2) == buf2.take(n2a) + buf2.skip(n2a).take(n2b));
                        assert(buf1.take(prefix1).take(n1a) == buf1.take(n1a));
                        assert(buf2.take(prefix2).take(n2a) == buf2.take(n2a));
                    }
                }
            }
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

impl<C: SPRoundTripDps + NonTailFmt> SPRoundTripDps for super::OptionalEnd<C> {
    open spec fn unambiguous(&self) -> bool {
        Optional(self.0, super::Eof).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
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

impl<C: EquivSerializersGeneral> EquivSerializers for super::OptionalEnd<C> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Optional(self.0, super::Eof).lemma_serialize_equiv_on_empty((v, ()));
    }
}

impl<C: SPRoundTripDps + NonTailFmt> SPRoundTripDps for super::RepeatTillEnd<C> {
    open spec fn unambiguous(&self) -> bool {
        Repeat(self.0, super::Eof).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
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

impl<C: EquivSerializersGeneral> EquivSerializers for super::RepeatTillEnd<C> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Repeat(self.0, super::Eof).lemma_serialize_equiv_on_empty((v, ()));
    }
}

} // verus!
