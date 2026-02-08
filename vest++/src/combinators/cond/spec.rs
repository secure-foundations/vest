use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner: SpecParser> SpecParser for super::Cond<Inner> {
    type PVal = Inner::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if self.0 {
            self.1.spec_parse(ibuf)
        } else {
            None
        }
    }
}

impl<Inner: Consistency> Consistency for super::Cond<Inner> {
    type Val = Inner::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0 && self.1.consistent(v)
    }
}

impl<Inner: GoodParser> GoodParser for super::Cond<Inner> {
    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        if self.0 {
            self.1.lemma_parse_len_bound(ibuf);
        }
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        if self.0 {
            self.1.lemma_parse_byte_len(ibuf);
        }
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        if self.0 {
            self.1.lemma_parse_consistent(ibuf);
            if let Some((_, v)) = self.1.spec_parse(ibuf) {
                assert(self.consistent(v));
            }
        }
    }
}

impl<Inner: SpecSerializerDps> SpecSerializerDps for super::Cond<Inner> {
    type ST = Inner::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.1.spec_serialize_dps(v, obuf)
    }
}

impl<Inner: SpecSerializer> SpecSerializer for super::Cond<Inner> {
    type SVal = Inner::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.1.spec_serialize(v)
    }
}

impl<Inner: Serializability> Serializability for super::Cond<Inner> {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        self.0 && self.1.serializable(v, obuf)
    }
}

impl<Inner: Unambiguity> Unambiguity for super::Cond<Inner> {
    open spec fn unambiguous(&self) -> bool {
        self.1.unambiguous()
    }
}

impl<Inner: GoodSerializerDps> GoodSerializerDps for super::Cond<Inner> {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner: GoodSerializer> GoodSerializer for super::Cond<Inner> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.1.lemma_serialize_len(v);
    }
}

impl<Inner: SpecByteLen> SpecByteLen for super::Cond<Inner> {
    type T = Inner::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.1.byte_len(v)
    }
}

} // verus!
