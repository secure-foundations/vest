use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Terminated<A, B> where A: SpecParser, B: SpecParser {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match (self.0, self.1).spec_parse(ibuf) {
            Some((n, (va, _vb))) => Some((n, va)),
            None => None,
        }
    }
}

impl<A, B> Consistency for super::Terminated<A, B> where A: Consistency, B: Consistency {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.0.consistent(v)
        &&& exists|vb: B::Val| self.1.consistent(vb)
    }
}

impl<A, B> SoundParser for super::Terminated<A, B> where
    A: SoundParser,
    B: SoundParser + AdmitsUniqueVal,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_sound_consumption(ibuf);
        (self.0, self.1).lemma_parse_sound_value(ibuf);
        if let Some((n, (va, vb))) = (self.0, self.1).spec_parse(ibuf) {
            let vb_wit = choose|vb_wit: B::T| self.1.consistent(vb_wit);
            self.1.lemma_unique_consistent_val(vb_wit, vb);
            assert(self.byte_len(va) == (self.0, self.1).byte_len((va, vb)));
            assert(n == self.byte_len(va));
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Terminated<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps + Consistency<Val = B::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let vb = choose|vb: B::ST| #![auto] self.1.consistent(vb);
        (self.0, self.1).spec_serialize_dps((v, vb), obuf)
    }
}

impl<A, B> SpecSerializer for super::Terminated<A, B> where
    A: SpecSerializer,
    B: SpecSerializer + Consistency<Val = B::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let vb = choose|vb: B::SVal| self.1.consistent(vb);
        (self.0, self.1).spec_serialize((v, vb))
    }
}

impl<A, B> Unambiguity for super::Terminated<A, B> where A: Unambiguity, B: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        (self.0, self.1).unambiguous()
    }
}

impl<A, B> NonTailFmt for super::Terminated<A, B> where
    A: NonTailFmt,
    B: NonTailFmt + Consistency<Val = B::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] self.1.consistent(vb);
        (self.0, self.1).lemma_serialize_dps_prepend((v, vb), obuf);

    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] self.1.consistent(vb);
        (self.0, self.1).lemma_serialize_dps_len((v, vb), obuf);
    }
}

impl<A, B> GoodSerializer for super::Terminated<A, B> where
    A: GoodSerializer,
    B: GoodSerializer + Consistency<Val = B::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let vb = choose|vb: B::SVal| #![auto] self.1.consistent(vb);
        (self.0, self.1).lemma_serialize_len((v, vb));
    }
}

impl<A, B> SpecByteLen for super::Terminated<A, B> where
    A: SpecByteLen,
    B: SpecByteLen + Consistency<Val = B::T>,
 {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let vb = choose|vb: B::T| self.1.consistent(vb);
        (self.0, self.1).byte_len((v, vb))
    }
}

} // verus!
