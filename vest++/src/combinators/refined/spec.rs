use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred: SpecPred<A::PT>> SpecParser for super::Refined<A, Pred> where A: SpecParser {
    type PT = Subset<A::PT, Pred>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if self.pred.apply(v) => Some((n, Subset { val: v, pred: self.pred })),
            _ => None,
        }
    }
}

impl<A: GoodParser, Pred: SpecPred<A::PT>> GoodParser for super::Refined<A, Pred> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
    }
}

impl<A, Pred: SpecPred<A::ST>> SpecSerializerDps for super::Refined<A, Pred> where
    A: SpecSerializerDps,
 {
    type ST = Subset<A::ST, Pred>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v.val, obuf)
    }
}

impl<A, Pred: SpecPred<A::ST>> SpecSerializer for super::Refined<A, Pred> where A: SpecSerializer {
    type ST = Subset<A::ST, Pred>;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        self.inner.spec_serialize(v.val)
    }
}

impl<A: Serializability, Pred: SpecPred<A::ST>> Serializability for super::Refined<A, Pred> {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        &&& v.pred == self.pred
        &&& self.inner.serializable(v.val, obuf)
    }
}

impl<A: Unambiguity, Pred: SpecPred<A::ST>> Unambiguity for super::Refined<A, Pred> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.inner.unambiguous()
        &&& forall|v: Self::ST| v.pred == self.pred
    }
}

impl<A: GoodSerializerDps, Pred: SpecPred<A::ST>> GoodSerializerDps for super::Refined<A, Pred> {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_buf(v.val, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(v.val, obuf);
    }
}

impl<A: GoodSerializer, Pred: SpecPred<A::ST>> GoodSerializer for super::Refined<A, Pred> {
    proof fn lemma_serialize_len(&self, v: Self::ST) {
        self.inner.lemma_serialize_len(v.val);
    }
}

impl<A: SpecByteLen, Pred: SpecPred<A::T>> SpecByteLen for super::Refined<A, Pred> {
    type T = Subset<A::T, Pred>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(v.val)
    }
}

impl<Inner> SpecParser for super::Tag<Inner, Inner::PT> where Inner: SpecParser {
    type PT = ();

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if v == self.tag => Some((n, ())),
            _ => None,
        }
    }
}

impl<Inner: GoodParser> GoodParser for super::Tag<Inner, Inner::PT> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
    }
}

impl<Inner> SpecSerializerDps for super::Tag<Inner, Inner::ST> where Inner: SpecSerializerDps {
    type ST = ();

    open spec fn spec_serialize_dps(&self, _v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.tag, obuf)
    }
}

impl<Inner> SpecSerializer for super::Tag<Inner, Inner::ST> where Inner: SpecSerializer {
    type ST = ();

    open spec fn spec_serialize(&self, _v: Self::ST) -> Seq<u8> {
        self.inner.spec_serialize(self.tag)
    }
}

impl<Inner> Serializability for super::Tag<Inner, Inner::ST> where Inner: Serializability {
    open spec fn serializable(&self, _v: Self::ST, obuf: Seq<u8>) -> bool {
        &&& self.tag.wf()
        &&& self.inner.serializable(self.tag, obuf)
    }
}

impl<Inner: Unambiguity> Unambiguity for super::Tag<Inner, Inner::ST> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.inner.unambiguous()
        &&& self.tag.wf()
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

impl<Inner: GoodSerializer> GoodSerializer for super::Tag<Inner, Inner::ST> {
    proof fn lemma_serialize_len(&self, v: Self::ST) {
        self.inner.lemma_serialize_len(self.tag);
    }
}

impl<Inner: SpecByteLen> SpecByteLen for super::Tag<Inner, Inner::T> {
    type T = ();

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(self.tag)
    }
}

} // verus!
