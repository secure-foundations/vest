use crate::{
    combinators::{mapped::spec::*, Mapped, Pair, Refined, TryMap},
    core::{proof::*, spec::*},
};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

pub open spec fn preceded<FmtA, FmtB, A, B, const CHECK: bool>(
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
                if CHECK {
                    pair.0 == a_val
                } else {
                    true
                },
        },
        mapper: BiMap(|pair: (A, B)| pair.1, |b| (a_val, b)),
    }
}

impl<A, AVal, B, const CHECK: bool> SpecParser for super::Preceded2<A, AVal, B, CHECK> where
    A: SpecParser,
    AVal: DeepView<V = A::PVal>,
    B: SpecParser,
 {
    type PVal = B::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.spec_parse(ibuf)
    }
}

impl<A, AVal, B, const CHECK: bool> SpecSerializerDps for super::Preceded2<A, AVal, B, CHECK> where
    A: SpecSerializerDps,
    AVal: DeepView<V = A::SValue>,
    B: SpecSerializerDps,
 {
    type SValue = B::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.spec_serialize_dps(v, obuf)
    }
}

impl<A, AVal, B, const CHECK: bool> SpecSerializer for super::Preceded2<A, AVal, B, CHECK> where
    A: SpecSerializer,
    AVal: DeepView<V = A::SVal>,
    B: SpecSerializer,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.spec_serialize(v)
    }
}

impl<A, AVal, B, const CHECK: bool> Consistency for super::Preceded2<A, AVal, B, CHECK> where
    A: Consistency,
    AVal: DeepView<V = A::Val>,
    B: Consistency,
 {
    type Val = B::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.consistent(v)
    }
}

impl<A, AVal, B, const CHECK: bool> SafeParser for super::Preceded2<A, AVal, B, CHECK> where
    A: SafeParser,
    AVal: DeepView<V = A::PVal>,
    B: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_parse_safe(ibuf);
    }
}

impl<A, AVal, B> SoundParser for super::Preceded2<A, AVal, B, true> where
    A: SoundParser,
    AVal: DeepView<V = A::PVal>,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        // When CHECK is true, we check that the value parsed by A is exactly a_val, making the `BiMap` `lossless` (the sound_inv condition
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

impl<A, AVal, B> SoundParser for super::Preceded2<A, AVal, B, false> where
    A: SoundParser + AdmitsUniqueVal,
    AVal: DeepView<V = A::PVal>,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& Pair(self.a, self.b).sound_inv()
        &&& self.a.consistent(self.a_val.deep_view())
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        pair.lemma_parse_sound_consumption(ibuf);
        pair.lemma_parse_sound_value(ibuf);
        if let Some((n, vb)) = self.spec_parse(ibuf) {
            let (_m, p) = pair.spec_parse(ibuf)->0;
            self.a.lemma_unique_consistent_val(self.a_val.deep_view(), p.0);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        pair.lemma_parse_sound_value(ibuf);
    }
}

impl<A, AVal, B, const CHECK: bool> NonTailFmt for super::Preceded2<A, AVal, B, CHECK> where
    A: NonTailFmt,
    AVal: DeepView<V = A::SValue>,
    B: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, AVal, B, const CHECK: bool> GoodSerializer for super::Preceded2<A, AVal, B, CHECK> where
    A: GoodSerializer,
    AVal: DeepView<V = A::SVal>,
    B: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_serialize_len(v);
    }
}

impl<A, AVal, B, const CHECK: bool> SpecByteLen for super::Preceded2<A, AVal, B, CHECK> where
    A: SpecByteLen,
    AVal: DeepView<V = A::T>,
    B: SpecByteLen,
 {
    type T = B::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.byte_len(v)
    }
}

impl<A, AVal, B, const CHECK: bool> StaticByteLen for super::Preceded2<A, AVal, B, CHECK> where
    A: StaticByteLen,
    AVal: DeepView<V = A::T>,
    B: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        <Pair<A, B> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val.deep_view());
        fmt.lemma_static_len_matches_byte_len(v);
    }
}

impl<A, AVal, B, const CHECK: bool> ValueByteLen for super::Preceded2<A, AVal, B, CHECK> where
    A: StaticByteLen,
    AVal: DeepView<V = A::T>,
    B: ValueByteLen,
 {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::static_byte_len() + B::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        assert(self.byte_len(v) == Pair(self.a, self.b).byte_len((self.a_val.deep_view(), v)));
        self.a.lemma_static_len_matches_byte_len(self.a_val.deep_view());
        self.b.lemma_value_len_matches_byte_len(v);
    }
}

} // verus!
