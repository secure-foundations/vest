use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred> SpecParser for super::Refined<A, Pred> where A: SpecParser, Pred: SpecPred<A::PVal> {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if self.pred.apply(v) => Some((n, v)),
            _ => None,
        }
    }
}

impl<A, Pred> Consistency for super::Refined<A, Pred> where A: Consistency, Pred: SpecPred<A::Val> {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.inner.consistent(v) && self.pred.apply(v)
    }
}

impl<A, Pred> GoodParser for super::Refined<A, Pred> where A: GoodParser, Pred: SpecPred<A::PVal> {
    open spec fn inv(&self) -> bool {
        self.inner.inv()
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_len_bound(ibuf);
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_byte_len(ibuf);
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_consistent(ibuf);
    }
}

impl<A, Pred> SpecSerializerDps for super::Refined<A, Pred> where
    A: SpecSerializerDps,
    Pred: SpecPred<A::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }
}

impl<A, Pred> SpecSerializer for super::Refined<A, Pred> where
    A: SpecSerializer,
    Pred: SpecPred<A::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<A, Pred> Serializability for super::Refined<A, Pred> where
    A: Serializability + Consistency<Val = A::ST>,
    Pred: SpecPred<A::ST>,
 {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        self.inner.consistent(v) && self.pred.apply(v) && self.inner.serializable(v, obuf)
    }
}

impl<A, Pred> Unambiguity for super::Refined<A, Pred> where
    A: Unambiguity,
    Pred: SpecPred<A::PVal>,
 {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<A, Pred> GoodSerializerDps for super::Refined<A, Pred> where
    A: GoodSerializerDps,
    Pred: SpecPred<A::ST>,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, Pred> GoodSerializer for super::Refined<A, Pred> where
    A: GoodSerializer,
    Pred: SpecPred<A::SVal>,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len(v);
    }
}

impl<A, Pred> SpecByteLen for super::Refined<A, Pred> where A: SpecByteLen, Pred: SpecPred<A::T> {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(v)
    }
}

impl<Inner> SpecParser for super::Tag<Inner, Inner::PVal> where Inner: SpecParser {
    type PVal = ();

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if v == self.tag => Some((n, ())),
            _ => None,
        }
    }
}

impl<Inner> Consistency for super::Tag<Inner, Inner::Val> where Inner: Consistency {
    type Val = ();

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        self.inner.consistent(self.tag)
    }
}

impl<Inner> AdmitsUniqueVal for super::Tag<Inner, Inner::Val> where Inner: Consistency {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
    }
}

impl<Inner> GoodParser for super::Tag<Inner, Inner::PVal> where Inner: GoodParser {
    open spec fn inv(&self) -> bool {
        self.inner.inv()
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_len_bound(ibuf);
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_byte_len(ibuf);
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_consistent(ibuf);
    }
}

impl<Inner> SpecSerializerDps for super::Tag<Inner, Inner::ST> where Inner: SpecSerializerDps {
    type ST = ();

    open spec fn spec_serialize_dps(&self, _v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.tag, obuf)
    }
}

impl<Inner> SpecSerializer for super::Tag<Inner, Inner::SVal> where Inner: SpecSerializer {
    type SVal = ();

    open spec fn spec_serialize(&self, _v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(self.tag)
    }
}

impl<Inner> Unambiguity for super::Tag<Inner, Inner::PVal> where Inner: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<Inner> GoodSerializerDps for super::Tag<Inner, Inner::ST> where Inner: GoodSerializerDps {
    proof fn lemma_serialize_dps_buf(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_buf(self.tag, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(self.tag, obuf);
    }
}

impl<Inner> GoodSerializer for super::Tag<Inner, Inner::SVal> where Inner: GoodSerializer {
    proof fn lemma_serialize_len(&self, _v: Self::SVal) {
        self.inner.lemma_serialize_len(self.tag);
    }
}

impl<Inner> SpecByteLen for super::Tag<Inner, Inner::T> where Inner: SpecByteLen {
    type T = ();

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        self.inner.byte_len(self.tag)
    }
}

} // verus!
