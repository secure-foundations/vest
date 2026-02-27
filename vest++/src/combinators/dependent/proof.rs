use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Head, Tail> SPRoundTripDps for super::Bind<Head, Tail> where
    Head: SPRoundTripDps + NonTailFmt,
    Tail: super::DepCombinator<Key = Head::T>,
    Tail::Body: SPRoundTripDps<T = Tail::Val>,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
        let key = self.1.recover(value);
        let next = self.1.apply(key);
        let next_buf = next.spec_serialize_dps(value, obuf);
        let serialized = self.0.spec_serialize_dps(key, next_buf);
        assert(self.0.consistent(key) && next.consistent(value));
        next.theorem_serialize_dps_parse_roundtrip(value, obuf);
        self.0.theorem_serialize_dps_parse_roundtrip(key, next_buf);
        self.0.lemma_serialize_dps_prepend(key, next_buf);
        self.0.lemma_serialize_dps_len(key, next_buf);
        if let Some((n0, _)) = self.0.spec_parse(serialized) {
            assert(n0 == serialized.len() - next_buf.len());
            assert(serialized.skip(n0) == next_buf);
        }
    }
}

impl<Head, Tail> NonMalleable for super::Bind<Head, Tail> where
    Head: NonMalleable,
    Tail: super::DepCombinator<Key = Head::T>,
    Tail::Body: NonMalleable<T = Tail::Val>,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (n1a, k1) = self.0.spec_parse(buf1)->0;
                    let (n2a, k2) = self.0.spec_parse(buf2)->0;
                    let body1 = self.1.apply(k1);
                    let body2 = self.1.apply(k2);
                    let (n1b, v) = body1.spec_parse(buf1.skip(n1a))->0;
                    let (n2b, v) = body2.spec_parse(buf2.skip(n2a))->0;
                    self.0.lemma_parse_sound_value(buf1);
                    self.0.lemma_parse_sound_value(buf2);
                    body1.lemma_parse_sound_value(buf1.skip(n1a));
                    body2.lemma_parse_sound_value(buf2.skip(n2a));
                    self.1.lemma_recover_consistent(k1, v);
                    self.1.lemma_recover_consistent(k2, v);
                    assert(k1 == k2 && body1 == body2);
                    let body = body1;
                    self.0.lemma_parse_safe(buf1);
                    self.0.lemma_parse_safe(buf2);
                    body.lemma_parse_safe(buf1.skip(n1a));
                    body.lemma_parse_safe(buf2.skip(n2a));
                    self.0.lemma_parse_non_malleable(buf1, buf2);
                    body.lemma_parse_non_malleable(buf1.skip(n1a), buf2.skip(n2a));
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

impl<Head, Tail> NoLookAhead for super::Bind<Head, Tail> where
    Head: NoLookAhead,
    Tail: super::DepCombinator<Key = Head::PVal>,
    Tail::Body: NoLookAhead<T = Tail::Val>,
 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        broadcast use vstd::seq_lib::group_seq_properties;

        use crate::combinators::tuple::proof::lemma_take_skip;

        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    if let Some((n1, key)) = self.0.spec_parse(i1) {
                        let body = self.1.apply(key);
                        if let Some((n2, _v2)) = body.spec_parse(i1.skip(n1)) {
                            self.lemma_parse_safe(i1);
                            self.0.lemma_parse_safe(i1);
                            body.lemma_parse_safe(i1.skip(n1));
                            assert(i2.take(n1) == i1.take(n1));
                            self.0.lemma_no_lookahead(i1, i2);
                            assert(i2.skip(n1).take(n2) == i1.skip(n1).take(n2)) by {
                                lemma_take_skip(i1, n1, n2);
                                lemma_take_skip(i2, n1, n2);
                            };
                            body.lemma_no_lookahead(i1.skip(n1), i2.skip(n1));
                            assert(self.spec_parse(i2) == Some((n, v)));
                        }
                    }
                }
            }
        }
    }
}

impl<Head, Tail> EquivSerializersGeneral for super::Bind<Head, Tail> where
    Head: EquivSerializersGeneral,
    Tail: super::DepCombinator<Key = Head::SVal>,
    Tail::Body: EquivSerializersGeneral<SVal = Tail::Val>,
 {
    proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
        let key = self.1.recover(value);
        let next = self.1.apply(key);
        let obuf1 = next.spec_serialize_dps(value, obuf);
        next.lemma_serialize_equiv(value, obuf);
        self.0.lemma_serialize_equiv(key, obuf1);
    }
}

impl<Head, Tail> EquivSerializers for super::Bind<Head, Tail> where
    Head: EquivSerializersGeneral,
    Tail: super::DepCombinator<Key = Head::SVal>,
    Tail::Body: EquivSerializers<SVal = Tail::Val>,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
        let key = self.1.recover(value);
        let next = self.1.apply(key);
        let empty = Seq::empty();
        let obuf = next.spec_serialize_dps(value, empty);
        next.lemma_serialize_equiv_on_empty(value);
        self.0.lemma_serialize_equiv(key, obuf);
    }
}

} // verus!
