use crate::{
    combinators::{mapped::spec::*, Mapped, Pair, Refined, TryMap},
    core::{proof::*, spec::*},
};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Preceded<A, B> where A: SpecParser, B: SpecParser {
    type PVal = B::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |pair: (A::PVal, B::PVal)| pair.1,
        }.spec_parse(ibuf)
    }
}

impl<A, B> SpecSerializerDps for super::Preceded<A, B> where
    A: SpecSerializerDps + Consistency<Val = A::SValue>,
    B: SpecSerializerDps,
 {
    type SValue = B::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |b: B::SValue| (choose|a: A::SValue| self.0.consistent(a), b),
        }.spec_serialize_dps(v, obuf)
    }
}

impl<A, B> SpecSerializer for super::Preceded<A, B> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |b: B::SVal| (choose|a: A::SVal| self.0.consistent(a), b),
        }.spec_serialize(v)
    }
}

impl<A, B> Consistency for super::Preceded<A, B> where A: Consistency, B: Consistency {
    type Val = B::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.1.consistent(v)
        &&& exists|va: A::Val| self.0.consistent(va)
    }
}

impl<A, B> SafeParser for super::Preceded<A, B> where A: SafeParser, B: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        Pair(self.0, self.1).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_parse_safe(ibuf);
    }
}

impl<A, B> SoundParser for super::Preceded<A, B> where
    A: SoundParser + AdmitsUniqueVal,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        Pair(self.0, self.1).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.0, self.1);
        pair.lemma_parse_sound_consumption(ibuf);
        pair.lemma_parse_sound_value(ibuf);
        if let Some((n, (va, vb))) = pair.spec_parse(ibuf) {
            let va_wit = choose|va_wit: A::T| self.0.consistent(va_wit);
            self.0.lemma_unique_consistent_val(va_wit, va);
            assert(self.byte_len(vb) == pair.byte_len((va, vb)));
            assert(n == self.byte_len(vb));
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> NonTailFmt for super::Preceded<A, B> where
    A: NonTailFmt + Consistency<Val = A::SValue>,
    B: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        Pair(self.0, self.1).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let va = choose|va: A::SValue| #![auto] self.0.consistent(va);
        Pair(self.0, self.1).lemma_serialize_dps_prepend((va, v), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let va = choose|va: A::SValue| #![auto] self.0.consistent(va);
        Pair(self.0, self.1).lemma_serialize_dps_len((va, v), obuf);
    }
}

impl<A, B> GoodSerializer for super::Preceded<A, B> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        Pair(self.0, self.1).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let va = choose|va: A::SVal| #![auto] self.0.consistent(va);
        Pair(self.0, self.1).lemma_serialize_len((va, v));
    }
}

impl<A, B> SpecByteLen for super::Preceded<A, B> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen,
 {
    type T = B::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let va = choose|va: A::T| self.0.consistent(va);
        Pair(self.0, self.1).byte_len((va, v))
    }
}

impl<A, B> StaticByteLen for super::Preceded<A, B> where A: StaticByteLen, B: StaticByteLen {
    open spec fn static_byte_len() -> nat {
        <Pair<A, B> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let va = choose|va: A::T| self.0.consistent(va);
        assert(self.byte_len(v) == Pair(self.0, self.1).byte_len((va, v)));
        self.0.lemma_static_len_matches_byte_len(va);
        self.1.lemma_static_len_matches_byte_len(v);
    }
}

impl<A, B> ValueByteLen for super::Preceded<A, B> where A: StaticByteLen, B: ValueByteLen {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::static_byte_len() + B::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        let va = choose|va: A::T| self.0.consistent(va);
        assert(self.byte_len(v) == Pair(self.0, self.1).byte_len((va, v)));
        self.0.lemma_static_len_matches_byte_len(va);
        self.1.lemma_value_len_matches_byte_len(v);
    }
}

pub open spec fn preceded<FmtA, FmtB, A, B, const NON_MALLEABLE: bool>(
    a: FmtA,
    b: FmtB,
    a_val: A,
) -> Mapped<
    Refined<Pair<FmtA, FmtB>, spec_fn((A, B)) -> bool>,
    BiMap<spec_fn((A, B)) -> B, spec_fn(B) -> (A, B)>,
> {
    Mapped {
        inner: Refined {
            inner: Pair(a, b),
            pred: |pair: (A, B)|
                if NON_MALLEABLE {
                    pair.0 == a_val
                } else {
                    true
                },
        },
        mapper: BiMap(|pair: (A, B)| pair.1, |b| (a_val, b)),
    }
}

impl<A, AVal, B, const NONMAL: bool> SpecParser for super::Preceded2<A, AVal, B, NONMAL> where
    A: SpecParser,
    AVal: DeepView<V = A::PVal>,
    B: SpecParser,
 {
    type PVal = B::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.spec_parse(ibuf)
    }
}

impl<A, AVal, B, const NONMAL: bool> SpecSerializerDps for super::Preceded2<
    A,
    AVal,
    B,
    NONMAL,
> where A: SpecSerializerDps, AVal: DeepView<V = A::SValue>, B: SpecSerializerDps {
    type SValue = B::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.spec_serialize_dps(v, obuf)
    }
}

impl<A, AVal, B, const NONMAL: bool> SpecSerializer for super::Preceded2<A, AVal, B, NONMAL> where
    A: SpecSerializer,
    AVal: DeepView<V = A::SVal>,
    B: SpecSerializer,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.spec_serialize(v)
    }
}

impl<A, AVal, B, const NONMAL: bool> Consistency for super::Preceded2<A, AVal, B, NONMAL> where
    A: Consistency,
    AVal: DeepView<V = A::Val>,
    B: Consistency,
 {
    type Val = B::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.consistent(v)
    }
}

impl<A, AVal, B, const NONMAL: bool> SafeParser for super::Preceded2<A, AVal, B, NONMAL> where
    A: SafeParser,
    AVal: DeepView<V = A::PVal>,
    B: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_parse_safe(ibuf);
    }
}

impl<A, AVal, B> SoundParser for super::Preceded2<A, AVal, B, true> where
    A: SoundParser,
    AVal: DeepView<V = A::PVal>,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        // When NONMAL is true, we check that the value parsed by A is exactly a_val, making the `BiMap` `lossless` (the sound_inv condition
        // required by `Mapped<Inner, BiMap<M, MRev>>`).
        // As a result, `sound_inv` for `Mapped<Inner, BiMap<M, MRev>>` holds as long as `sound_inv` for `Inner` holds.
        Pair(self.a, self.b).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, true>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, true>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_parse_sound_value(ibuf);
    }
}

impl<A, AVal, B, const NONMAL: bool> NonTailFmt for super::Preceded2<A, AVal, B, NONMAL> where
    A: NonTailFmt,
    AVal: DeepView<V = A::SValue>,
    B: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, AVal, B, const NONMAL: bool> GoodSerializer for super::Preceded2<A, AVal, B, NONMAL> where
    A: GoodSerializer,
    AVal: DeepView<V = A::SVal>,
    B: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_serialize_len(v);
    }
}

impl<A, AVal, B, const NONMAL: bool> SpecByteLen for super::Preceded2<A, AVal, B, NONMAL> where
    A: SpecByteLen,
    AVal: DeepView<V = A::T>,
    B: SpecByteLen,
 {
    type T = B::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.byte_len(v)
    }
}

impl<A, AVal, B, const NONMAL: bool> StaticByteLen for super::Preceded2<A, AVal, B, NONMAL> where
    A: StaticByteLen,
    AVal: DeepView<V = A::T>,
    B: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        <Pair<A, B> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let fmt = preceded::<_, _, _, _, NONMAL>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_static_len_matches_byte_len(v);
    }
}

} // verus!
