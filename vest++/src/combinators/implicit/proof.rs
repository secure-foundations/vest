use super::spec::*;
use crate::combinators::tuple::proof::lemma_take_skip;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTripDps for super::Implicit<A, spec_fn(A::T) -> B> where
    A: SPRoundTripDps + GoodSerializerDps,
    B: SPRoundTripDps,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
        let a = choose|a: A::T| #![auto] self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        let next_buf = next.spec_serialize_dps(value, obuf);
        let serialized = self.0.spec_serialize_dps(a, next_buf);
        next.theorem_serialize_dps_parse_roundtrip(value, obuf);
        self.0.theorem_serialize_dps_parse_roundtrip(a, next_buf);
        self.0.lemma_serialize_dps_buf(a, next_buf);
        self.0.lemma_serialize_dps_len(a, next_buf);
        if let Some((n0, _)) = self.0.spec_parse(serialized) {
            assert(n0 == serialized.len() - next_buf.len());
            assert(serialized.skip(n0) == next_buf);
        }
    }
}

impl<A, B> EquivSerializersGeneral for super::Implicit<A, spec_fn(A::SVal) -> B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializersGeneral + Consistency<Val = B::SVal>,
 {
    proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
        let a = choose|a: A::SVal| #![auto] self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        let obuf1 = next.spec_serialize_dps(value, obuf);
        next.lemma_serialize_equiv(value, obuf);
        self.0.lemma_serialize_equiv(a, obuf1);
    }
}

impl<A, B> NoLookAhead for super::Implicit<A, spec_fn(A::PVal) -> B> where
    A: NoLookAhead,
    B: NoLookAhead,
    Self: super::LosslessImplicit<A, B>,
 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        broadcast use vstd::seq_lib::group_seq_properties;

        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    if let Some((n1, a)) = self.0.spec_parse(i1) {
                        let next = (self.1)(a);
                        if let Some((n2, v_next)) = next.spec_parse(i1.skip(n1)) {
                            self.lemma_parse_len_bound(i1);
                            self.0.lemma_parse_len_bound(i1);
                            next.lemma_parse_len_bound(i1.skip(n1));
                            assert(i2.take(n1) == i1.take(n1));
                            self.0.lemma_no_lookahead(i1, i2);
                            assert(i2.skip(n1).take(n2) == i1.skip(n1).take(n2)) by {
                                lemma_take_skip(i1, n1, n2);
                                lemma_take_skip(i2, n1, n2);
                            };
                            next.lemma_no_lookahead(i1.skip(n1), i2.skip(n1));
                            assert(self.spec_parse(i2) == Some((n, v)));
                        }
                    }
                }
            }
        }
    }
}

impl<A, B> EquivSerializers for super::Implicit<A, spec_fn(A::SVal) -> B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializers + Consistency<Val = B::SVal>,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
        let a = choose|a: A::SVal| #![auto] self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        let empty = Seq::empty();
        let obuf = next.spec_serialize_dps(value, empty);
        next.lemma_serialize_equiv_on_empty(value);
        self.0.lemma_serialize_equiv(a, obuf);
    }
}

impl<A, B> NonMalleable for super::Implicit<A, spec_fn(A::PVal) -> B> where
    A: NonMalleable,
    B: NonMalleable,
    Self: super::LosslessImplicit<A, B>,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (n1a, a1) = self.0.spec_parse(buf1)->0;
                    let (n2a, a2) = self.0.spec_parse(buf2)->0;
                    let next1 = (self.1)(a1);
                    let next2 = (self.1)(a2);
                    let (n1b, v) = next1.spec_parse(buf1.skip(n1a))->0;
                    let (n2b, v) = next2.spec_parse(buf2.skip(n2a))->0;
                    self.0.lemma_parse_consistent(buf1);
                    self.0.lemma_parse_consistent(buf2);
                    next1.lemma_parse_consistent(buf1.skip(n1a));
                    next2.lemma_parse_consistent(buf2.skip(n2a));
                    <Self as super::LosslessImplicit<A, B>>::lemma_value_uniquely_determines_key(
                        self,
                        a1,
                        a2,
                        v,
                    );
                    assert(a1 == a2 && next1 == next2);
                    let next = next1;
                    self.0.lemma_parse_len_bound(buf1);
                    self.0.lemma_parse_len_bound(buf2);
                    next.lemma_parse_len_bound(buf1.skip(n1a));
                    next.lemma_parse_len_bound(buf2.skip(n2a));
                    self.0.lemma_parse_non_malleable(buf1, buf2);
                    next.lemma_parse_non_malleable(buf1.skip(n1a), buf2.skip(n2a));
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

impl<A, B> SPRoundTripDps for super::ImplicitAuto<
    A,
    spec_fn(A::T) -> B,
    spec_fn(B::T) -> A::T,
> where A: SPRoundTripDps + GoodSerializerDps, B: SPRoundTripDps {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
        let a = (self.2)(value);
        let next = (self.1)(a);
        let next_buf = next.spec_serialize_dps(value, obuf);
        let serialized = self.0.spec_serialize_dps(a, next_buf);
        assert(self.consistent(value));
        assert(self.0.consistent(a) && next.consistent(value));
        next.theorem_serialize_dps_parse_roundtrip(value, obuf);
        self.0.theorem_serialize_dps_parse_roundtrip(a, next_buf);
        self.0.lemma_serialize_dps_buf(a, next_buf);
        self.0.lemma_serialize_dps_len(a, next_buf);
        if let Some((n0, _)) = self.0.spec_parse(serialized) {
            assert(n0 == serialized.len() - next_buf.len());
            assert(serialized.skip(n0) == next_buf);
        }
    }
}

impl<A, B> NonMalleable for super::ImplicitAuto<
    A,
    spec_fn(A::T) -> B,
    spec_fn(B::T) -> A::T,
> where
    Self: GoodParser<T = B::T>,
    A: NonMalleable,
    B: NonMalleable,
    Self: super::LosslessImplicitAuto<A, B>,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (n1a, a1) = self.0.spec_parse(buf1)->0;
                    let (n2a, a2) = self.0.spec_parse(buf2)->0;
                    let next1 = (self.1)(a1);
                    let next2 = (self.1)(a2);
                    let (n1b, v) = next1.spec_parse(buf1.skip(n1a))->0;
                    let (n2b, v) = next2.spec_parse(buf2.skip(n2a))->0;
                    self.0.lemma_parse_consistent(buf1);
                    self.0.lemma_parse_consistent(buf2);
                    next1.lemma_parse_consistent(buf1.skip(n1a));
                    next2.lemma_parse_consistent(buf2.skip(n2a));
                    <Self as super::LosslessImplicitAuto<A, B>>::lemma_value_determines_key(
                        self,
                        a1,
                        a2,
                        v,
                    );
                    assert(a1 == a2 && next1 == next2);
                    let next = next1;
                    self.0.lemma_parse_len_bound(buf1);
                    self.0.lemma_parse_len_bound(buf2);
                    next.lemma_parse_len_bound(buf1.skip(n1a));
                    next.lemma_parse_len_bound(buf2.skip(n2a));
                    self.0.lemma_parse_non_malleable(buf1, buf2);
                    next.lemma_parse_non_malleable(buf1.skip(n1a), buf2.skip(n2a));
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

impl<A, B> EquivSerializersGeneral for super::ImplicitAuto<
    A,
    spec_fn(A::SVal) -> B,
    spec_fn(B::SVal) -> A::SVal,
> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializersGeneral + Consistency<Val = B::SVal>,
 {
    proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
        let a = (self.2)(value);
        let next = (self.1)(a);
        let obuf1 = next.spec_serialize_dps(value, obuf);
        next.lemma_serialize_equiv(value, obuf);
        self.0.lemma_serialize_equiv(a, obuf1);
    }
}

impl<A, B> EquivSerializers for super::ImplicitAuto<
    A,
    spec_fn(A::SVal) -> B,
    spec_fn(B::SVal) -> A::SVal,
> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializers + Consistency<Val = B::SVal>,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
        let a = (self.2)(value);
        let next = (self.1)(a);
        let empty = Seq::empty();
        let obuf = next.spec_serialize_dps(value, empty);
        next.lemma_serialize_equiv_on_empty(value);
        self.0.lemma_serialize_equiv(a, obuf);
    }
}

} // verus!
