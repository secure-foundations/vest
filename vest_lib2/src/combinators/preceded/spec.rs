use crate::{
    combinators::{mapped::spec::*, Mapped, Pair, Refined, TryMap},
    core::{proof::*, spec::*},
};
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
        inner: Refined(
            Pair(a, b),
            |pair: (A, B)|
                if CHECK {
                    pair.0 == a_val
                } else {
                    true
                },
        ),
        mapper: BiMap(|pair: (A, B)| pair.1, |b| (a_val, b)),
    }
}

impl<A, B, const CHECK: bool> SpecParser for super::Preceded<A, A::PVal, B, CHECK> where
    A: SpecParser,
    B: SpecParser,
 {
    type PVal = B::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.spec_parse(ibuf)
    }
}

impl<A, B, const CHECK: bool> SpecSerializerDps for super::Preceded<A, A::SValue, B, CHECK> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type SValue = B::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.spec_serialize_dps(v, obuf)
    }
}

impl<A, B, const CHECK: bool> SpecSerializer for super::Preceded<A, A::SVal, B, CHECK> where
    A: SpecSerializer,
    B: SpecSerializer,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.spec_serialize(v)
    }
}

impl<A, B, const CHECK: bool> Consistency for super::Preceded<A, A::Val, B, CHECK> where
    A: Consistency,
    B: Consistency,
 {
    type Val = B::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.consistent(v)
    }
}

impl<A, B, const CHECK: bool> SafeParser for super::Preceded<A, A::PVal, B, CHECK> where
    A: SafeParser,
    B: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_parse_safe(ibuf);
    }
}

impl<A, B> SoundParser for super::Preceded<A, A::PVal, B, true> where
    A: SoundParser,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        // When CHECK is true, we check that the value parsed by A is exactly a_val, making the `BiMap` `lossless` (the sound_inv condition
        // required by `Mapped<Inner, BiMap<M, MRev>>`).
        // As a result, `sound_inv` for `Mapped<Inner, BiMap<M, MRev>>` holds as long as `sound_inv` for `Inner` holds.
        Pair(self.a, self.b).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, true>(self.a, self.b, self.a_val);
        fmt.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, true>(self.a, self.b, self.a_val);
        fmt.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SoundParser for super::Preceded<A, A::PVal, B, false> where
    A: SoundParser + AdmitsUniqueVal,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& Pair(self.a, self.b).sound_inv()
        &&& self.a.consistent(self.a_val)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        pair.lemma_parse_sound_consumption(ibuf);
        pair.lemma_parse_sound_value(ibuf);
        if let Some((n, vb)) = self.spec_parse(ibuf) {
            let (_m, p) = pair.spec_parse(ibuf)->0;
            self.a.lemma_unique_consistent_val(self.a_val, p.0);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        pair.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B, const CHECK: bool> NonTailFmt for super::Preceded<A, A::SValue, B, CHECK> where
    A: NonTailFmt,
    B: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B, const CHECK: bool> GoodSerializer for super::Preceded<A, A::SVal, B, CHECK> where
    A: GoodSerializer,
    B: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_serialize_len(v);
    }
}

impl<A, B, const CHECK: bool> SpecByteLen for super::Preceded<A, A::T, B, CHECK> where
    A: SpecByteLen,
    B: SpecByteLen,
 {
    type T = B::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.byte_len(v)
    }
}

impl<A, B, const CHECK: bool> MinMaxByteLen for super::Preceded<A, A::T, B, CHECK> where
    A: MinMaxByteLen,
    B: MinMaxByteLen,
 {
    open spec fn min(&self) -> nat {
        preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val).min()
    }

    open spec fn max(&self) -> nat {
        preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val).max()
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
        preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val).lemma_min_max_byte_len(v);
    }
}

impl<A, B, const CHECK: bool> StaticByteLen for super::Preceded<A, A::T, B, CHECK> where
    A: StaticByteLen,
    B: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        <Pair<A, B> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_static_len_matches_byte_len(v);
    }
}

impl<A, B, const CHECK: bool> ValueByteLen for super::Preceded<A, A::T, B, CHECK> where
    A: StaticByteLen,
    B: ValueByteLen,
 {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::static_byte_len() + B::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        assert(self.byte_len(v) == Pair(self.a, self.b).byte_len((self.a_val, v)));
        self.a.lemma_static_len_matches_byte_len(self.a_val);
        self.b.lemma_value_len_matches_byte_len(v);
    }
}

} // verus!
