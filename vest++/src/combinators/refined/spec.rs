use crate::core::spec::{
    GoodParser, GoodSerializer, Serializability, SpecParser, SpecPred, SpecSerializer,
    SpecSerializerDps, SpecType, Subset,
};
use vstd::prelude::*;

verus! {

impl<A> SpecParser for super::Refined<A, SpecPred<A::PT>> where A: SpecParser {
    type PT = Subset<A::PT, SpecPred<A::PT>>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if (self.pred)(v) => Some((n, Subset { val: v, pred: self.pred })),
            _ => None,
        }
    }
}

impl<A: GoodParser> GoodParser for super::Refined<A, SpecPred<A::PT>> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
    }
}

impl<A> SpecSerializerDps for super::Refined<A, SpecPred<A::ST>> where A: SpecSerializerDps {
    type ST = Subset<A::ST, SpecPred<A::ST>>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v.val, obuf)
    }
}

impl<A> SpecSerializer for super::Refined<A, SpecPred<A::ST>> where A: SpecSerializer {
    type ST = Subset<A::ST, SpecPred<A::ST>>;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        self.inner.spec_serialize(v.val)
    }
}

impl<A: Serializability> Serializability for super::Refined<A, SpecPred<A::ST>> {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        &&& v.pred == self.pred
        &&& self.inner.serializable(v.val, obuf)
    }
}

impl<A: GoodSerializer> GoodSerializer for super::Refined<A, SpecPred<A::ST>> {
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        if v.wf() {
            self.inner.lemma_serialize_buf(v.val, obuf);
        }
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

impl<Inner> GoodSerializer for super::Tag<Inner, Inner::ST> where Inner: GoodSerializer {
    proof fn lemma_serialize_buf(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(self.tag, obuf);
    }
}

} // verus!
