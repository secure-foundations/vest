use crate::{
    combinators::{Mapped, Pair},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Terminated<A, B> where A: SpecParser, B: SpecParser {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |pair: (A::PVal, B::PVal)| pair.0,
        }.spec_parse(ibuf)
    }
}

impl<A, B> SpecSerializerDps for super::Terminated<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps + Consistency<Val = B::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |a: A::ST| (a, choose|vb: B::ST| self.1.consistent(vb)),
        }.spec_serialize_dps(v, obuf)
    }
}

impl<A, B> SpecSerializer for super::Terminated<A, B> where
    A: SpecSerializer,
    B: SpecSerializer + Consistency<Val = B::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Mapped {
            inner: Pair(self.0, self.1),
            mapper: |a: A::SVal| (a, choose|vb: B::SVal| self.1.consistent(vb)),
        }.spec_serialize(v)
    }
}

impl<A, B> Consistency for super::Terminated<A, B> where A: Consistency, B: Consistency {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.0.consistent(v)
        &&& exists|vb: B::Val| self.1.consistent(vb)
    }
}

impl<A, B> SafeParser for super::Terminated<A, B> where A: SafeParser, B: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        Pair(self.0, self.1).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_parse_safe(ibuf);
    }
}

impl<A, B> SoundParser for super::Terminated<A, B> where
    A: SoundParser,
    B: SoundParser + AdmitsUniqueVal,
 {
    open spec fn sound_inv(&self) -> bool {
        Pair(self.0, self.1).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let pair = Pair(self.0, self.1);
        pair.lemma_parse_sound_consumption(ibuf);
        pair.lemma_parse_sound_value(ibuf);
        if let Some((n, (va, vb))) = pair.spec_parse(ibuf) {
            let vb_wit = choose|vb_wit: B::T| self.1.consistent(vb_wit);
            self.1.lemma_unique_consistent_val(vb_wit, vb);
            assert(self.byte_len(va) == pair.byte_len((va, vb)));
            assert(n == self.byte_len(va));
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> Unambiguity for super::Terminated<A, B> where A: Unambiguity, B: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        Pair(self.0, self.1).unambiguous()
    }
}

impl<A, B> NonTailFmt for super::Terminated<A, B> where
    A: NonTailFmt,
    B: NonTailFmt + Consistency<Val = B::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        Pair(self.0, self.1).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] self.1.consistent(vb);
        Pair(self.0, self.1).lemma_serialize_dps_prepend((v, vb), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] self.1.consistent(vb);
        Pair(self.0, self.1).lemma_serialize_dps_len((v, vb), obuf);
    }
}

impl<A, B> GoodSerializer for super::Terminated<A, B> where
    A: GoodSerializer,
    B: GoodSerializer + Consistency<Val = B::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        Pair(self.0, self.1).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let vb = choose|vb: B::SVal| #![auto] self.1.consistent(vb);
        Pair(self.0, self.1).lemma_serialize_len((v, vb));
    }
}

impl<A, B> SpecByteLen for super::Terminated<A, B> where
    A: SpecByteLen,
    B: SpecByteLen + Consistency<Val = B::T>,
 {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let vb = choose|vb: B::T| self.1.consistent(vb);
        Pair(self.0, self.1).byte_len((v, vb))
    }
}

impl<A, B> StaticByteLen for super::Terminated<A, B> where A: StaticByteLen, B: StaticByteLen {
    open spec fn static_byte_len() -> nat {
        <Pair<A, B> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let vb = choose|vb: B::T| self.1.consistent(vb);
        assert(self.byte_len(v) == Pair(self.0, self.1).byte_len((v, vb)));
        self.0.lemma_static_len_matches_byte_len(v);
        self.1.lemma_static_len_matches_byte_len(vb);
    }
}

impl<A, B> ValueByteLen for super::Terminated<A, B> where A: ValueByteLen, B: StaticByteLen {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::value_byte_len(v) + B::static_byte_len()
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        let vb = choose|vb: B::T| self.1.consistent(vb);
        assert(self.byte_len(v) == Pair(self.0, self.1).byte_len((v, vb)));
        self.0.lemma_value_len_matches_byte_len(v);
        self.1.lemma_static_len_matches_byte_len(vb);
    }
}

} // verus!
