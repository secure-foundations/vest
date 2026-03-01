use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for (A, B) where A: SpecParser, B: SpecParser {
    type PVal = (A::PVal, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, v1)) => match self.1.spec_parse(ibuf.skip(n1)) {
                Some((n2, v2)) => Some((n1 + n2, (v1, v2))),
                None => None,
            },
            None => None,
        }
    }
}

impl<A, B> Consistency for (A, B) where A: Consistency, B: Consistency {
    type Val = (A::Val, B::Val);

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(v.0) && self.1.consistent(v.1)
    }
}

impl<A, B> SoundParser for (A, B) where A: SoundParser, B: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_safe(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_sound_consumption(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_sound_value(ibuf.skip(n1));
        }
    }
}

impl<A, B> SpecSerializerDps for (A, B) where A: SpecSerializerDps, B: SpecSerializerDps {
    type ST = (A::ST, B::ST);

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize_dps(v.0, self.1.spec_serialize_dps(v.1, obuf))
    }
}

impl<A, B> SpecSerializer for (A, B) where A: SpecSerializer, B: SpecSerializer {
    type SVal = (A::SVal, B::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.0.spec_serialize(v.0) + self.1.spec_serialize(v.1)
    }
}

impl<A, B> Unambiguity for (A, B) where A: Unambiguity, B: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        self.1.unambiguous() && self.0.unambiguous()
    }
}

impl<A, B> NonTailFmt for (A, B) where A: NonTailFmt, B: NonTailFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        let serialized0 = self.0.spec_serialize_dps(v.0, serialized1);
        self.1.lemma_serialize_dps_prepend(v.1, obuf);
        self.0.lemma_serialize_dps_prepend(v.0, serialized1);
        let witness1 = choose|wit1: Seq<u8>| self.1.spec_serialize_dps(v.1, obuf) == wit1 + obuf;
        let witness0 = choose|wit0: Seq<u8>|
            self.0.spec_serialize_dps(v.0, serialized1) == wit0 + serialized1;
        assert(serialized0 == witness0 + witness1 + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_len(v.1, obuf);
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        self.0.lemma_serialize_dps_len(v.0, serialized1);
    }
}

impl<A, B> GoodSerializer for (A, B) where A: GoodSerializer, B: GoodSerializer {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.1.lemma_serialize_len(v.1);
        self.0.lemma_serialize_len(v.0);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for (A, B) {
    type T = (A::T, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.0.byte_len(v.0) + self.1.byte_len(v.1)
    }
}

} // verus!
