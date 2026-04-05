use crate::{
    combinators::mapped::spec::{LosslessMapper, LossyMapper, Mapper},
    combinators::{Mapped, Pair},
    core::{proof::*, spec::*},
};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

impl<A, VA, VB> Mapper for super::PrecededMapper<A, VA, VB> where A: Consistency<Val = VA> {
    type In = (VA, VB);

    type Out = VB;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i.1
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        let va = choose|va: VA| self.0.consistent(va);
        (va, o)
    }

    open spec fn wf_in(&self, i: Self::In) -> bool {
        self.0.consistent(i.0)
    }

    open spec fn wf_out(&self, _o: Self::Out) -> bool {
        exists|va: VA| self.0.consistent(va)
    }
}

impl<A, VA, VB> LossyMapper for super::PrecededMapper<A, VA, VB> where A: Consistency<Val = VA> {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }
}

impl<A, VA, VB> LosslessMapper for super::PrecededMapper<A, VA, VB> where
    A: AdmitsUniqueVal<Val = VA>,
 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        let va_wit = choose|va_wit: VA| self.0.consistent(va_wit);
        assert(self.0.consistent(va_wit));
        self.0.lemma_unique_consistent_val(va_wit, i.0);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        assert(exists|va: VA| self.0.consistent(va)) by {
            assert(self.0.consistent(i.0));
        }
    }
}

impl<A, B> SpecParser for super::Preceded<A, B> where A: SpecParser, B: SpecParser {
    type PVal = B::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |pair: (A::PVal, B::PVal)| pair.1,
        }.spec_parse(ibuf)
    }
}

impl<A, B> Consistency for super::Preceded<A, B> where A: Consistency, B: Consistency {
    type Val = B::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        super::preceded_fmt::<A, B, A::Val, B::Val>(self.0, self.1).consistent(v)
    }
}

impl<A, B> SoundParser for super::Preceded<A, B> where
    A: SoundParser + AdmitsUniqueVal,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).lemma_parse_sound_consumption(
            ibuf,
        );
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Preceded<A, B> where
    A: SpecSerializerDps + Consistency<Val = A::ST>,
    B: SpecSerializerDps,
 {
    type ST = B::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        super::preceded_fmt::<A, B, A::ST, B::ST>(self.0, self.1).spec_serialize_dps(v, obuf)
    }
}

impl<A, B> SpecSerializer for super::Preceded<A, B> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(self.0, self.1).spec_serialize(v)
    }
}

impl<A, B> Unambiguity for super::Preceded<A, B> where A: Unambiguity, B: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        Pair(self.0, self.1).unambiguous()
    }
}

impl<A, B> NonTailFmt for super::Preceded<A, B> where
    A: NonTailFmt + Consistency<Val = A::ST>,
    B: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::ST, B::ST>(self.0, self.1).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::ST, B::ST>(self.0, self.1).lemma_serialize_dps_prepend(
            v,
            obuf,
        );
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::ST, B::ST>(self.0, self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B> GoodSerializer for super::Preceded<A, B> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(self.0, self.1).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(self.0, self.1).lemma_serialize_len(v);
    }
}

impl<A, B> SpecByteLen for super::Preceded<A, B> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen,
 {
    type T = B::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        super::preceded_fmt::<A, B, A::T, B::T>(self.0, self.1).byte_len(v)
    }
}

impl<A, B> StaticByteLen for super::Preceded<A, B> where A: StaticByteLen, B: StaticByteLen {
    open spec fn static_byte_len() -> nat {
        crate::combinators::Pair::<A, B>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        super::preceded_fmt::<A, B, A::T, B::T>(self.0, self.1).lemma_static_len_matches_byte_len(
            v,
        );
    }
}

} // verus!
