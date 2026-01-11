use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer,
    SpecSerializerDps, SpecType,
};
use vstd::prelude::*;

verus! {

impl<A: SpecType> SpecType for super::Refined<A> {
    type Type = A::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(v) && (self.pred)(v)
    }
}

impl<A> SpecParser for super::Refined<A> where 
    A: SpecType + SpecParser<PT = <A as SpecType>::Type>,
 {
    type PT = A::PT;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => {
                if (self.pred)(v) {
                    Some((n, v))
                } else {
                    None
                }
            },
            None => None,
        }
    }
}

impl<A: GoodParser> GoodParser for super::Refined<A> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
    }
}

impl<A> SpecSerializerDps for super::Refined<A> where
    A: SpecType + SpecSerializerDps<ST = <A as SpecType>::Type>,
 {
    type ST = A::ST;

    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        self.inner.serializable(v, obuf)
    }

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }
}

impl<A> SpecSerializer for super::Refined<A> where
    A: SpecType + SpecSerializer<ST = <A as SpecType>::Type>,
 {
    type ST = A::ST;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<A: GoodSerializer> GoodSerializer for super::Refined<A> {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(v, obuf);
    }
}

impl<Inner: SpecType> SpecType for super::Tag<Inner> {
    type Type = ();

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(self.tag)
    }
}

impl<Inner> SpecParser for super::Tag<Inner> where
    Inner: SpecType + SpecParser<PT = <Inner as SpecType>::Type>,
 {
    type PT = ();

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if v == self.tag => Some((n, ())),
            _ => None,
        }
    }
}

impl<Inner: GoodParser> GoodParser for super::Tag<Inner> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
    }
}

impl<Inner> SpecSerializerDps for super::Tag<Inner> where
    Inner: SpecType + SpecSerializerDps<ST = <Inner as SpecType>::Type>,
 {
    type ST = ();

    open spec fn serializable(&self, _v: Self::ST, obuf: Seq<u8>) -> bool {
        self.inner.serializable(self.tag, obuf)
    }

    open spec fn spec_serialize_dps(&self, _v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.tag, obuf)
    }
}

impl<Inner> SpecSerializer for super::Tag<Inner> where
    Inner: SpecType + SpecSerializer<ST = <Inner as SpecType>::Type>,
 {
    type ST = ();

    open spec fn spec_serialize(&self, _v: Self::ST) -> Seq<u8> {
        self.inner.spec_serialize(self.tag)
    }
}

impl<Inner: GoodSerializer> GoodSerializer for super::Tag<Inner> {
    proof fn lemma_serialize_buf(&self, _v: Self::Type, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(self.tag, obuf);
    }
}

} // verus!
