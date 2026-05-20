use crate::{
    combinators::{mapped::spec::*, Mapped, Pair, Refined},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

pub open spec fn terminated<FmtA, FmtB, A, B, const NON_MALLEABLE: bool>(
    a: FmtA,
    b: FmtB,
    b_val: B,
) -> Mapped<
    Refined<Pair<FmtA, FmtB>, spec_fn((A, B)) -> bool>,
    BiMap<spec_fn((A, B)) -> A, spec_fn(A) -> (A, B)>,
> {
    Mapped {
        inner: Refined(
            Pair(a, b),
            |pair: (A, B)|
                if NON_MALLEABLE {
                    pair.1 == b_val
                } else {
                    true
                },
        ),
        mapper: BiMap(|pair: (A, B)| pair.0, |a| (a, b_val)),
    }
}

impl<A, B, const CHECK: bool> SpecParser for super::Terminated<A, B, B::PVal, CHECK> where
    A: SpecParser,
    B: SpecParser,
 {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.spec_parse(ibuf)
    }
}

impl<A, B, const CHECK: bool> SpecSerializerDps for super::Terminated<A, B, B::SValue, CHECK> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type SValue = A::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.spec_serialize_dps(v, obuf)
    }
}

impl<A, B, const CHECK: bool> SpecSerializer for super::Terminated<A, B, B::SVal, CHECK> where
    A: SpecSerializer,
    B: SpecSerializer,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.spec_serialize(v)
    }
}

impl<A, B, const CHECK: bool> Consistency for super::Terminated<A, B, B::Val, CHECK> where
    A: Consistency,
    B: Consistency,
 {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.consistent(v)
    }
}

impl<A, B, const CHECK: bool> SafeParser for super::Terminated<A, B, B::PVal, CHECK> where
    A: SafeParser,
    B: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_parse_safe(ibuf);
    }
}

impl<A, B> SoundParser for super::Terminated<A, B, B::PVal, true> where
    A: SoundParser,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        Pair(self.a, self.b).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, true>(self.a, self.b, self.b_val);
        fmt.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, true>(self.a, self.b, self.b_val);
        fmt.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SoundParser for super::Terminated<A, B, B::PVal, false> where
    A: SoundParser,
    B: SoundParser + AdmitsUniqueVal,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& Pair(self.a, self.b).sound_inv()
        &&& self.b.consistent(self.b_val)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        pair.lemma_parse_sound_consumption(ibuf);
        pair.lemma_parse_sound_value(ibuf);
        if let Some((n, va)) = self.spec_parse(ibuf) {
            let (_m, p) = pair.spec_parse(ibuf)->0;
            self.b.lemma_unique_consistent_val(self.b_val, p.1);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        pair.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B, const CHECK: bool> NonTailFmt for super::Terminated<A, B, B::SValue, CHECK> where
    A: NonTailFmt,
    B: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B, const CHECK: bool> GoodSerializer for super::Terminated<A, B, B::SVal, CHECK> where
    A: GoodSerializer,
    B: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_serialize_len(v);
    }
}

impl<A, B, const CHECK: bool> SpecByteLen for super::Terminated<A, B, B::T, CHECK> where
    A: SpecByteLen,
    B: SpecByteLen,
 {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.byte_len(v)
    }
}

impl<A, B, const CHECK: bool> MinMaxByteLen for super::Terminated<A, B, B::T, CHECK> where
    A: MinMaxByteLen,
    B: MinMaxByteLen,
 {
    open spec fn min(&self) -> nat {
        terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val).min()
    }

    open spec fn max(&self) -> nat {
        terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val).max()
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
        terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val).lemma_min_max_byte_len(v);
    }
}

impl<A, B, const CHECK: bool> StaticByteLen for super::Terminated<A, B, B::T, CHECK> where
    A: StaticByteLen,
    B: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        <Pair<A, B> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_static_len_matches_byte_len(v);
    }
}

impl<A, B, const CHECK: bool> ValueByteLen for super::Terminated<A, B, B::T, CHECK> where
    A: ValueByteLen,
    B: StaticByteLen,
 {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::value_byte_len(v) + B::static_byte_len()
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        assert(self.byte_len(v) == Pair(self.a, self.b).byte_len((v, self.b_val)));
        self.a.lemma_value_len_matches_byte_len(v);
        self.b.lemma_static_len_matches_byte_len(self.b_val);
    }
}

} // verus!
