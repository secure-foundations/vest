use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, Serializability, SpecCombinator, SpecParser,
    SpecSerializer, SpecSerializerDps, SpecType,
};
use vstd::{prelude::*, seq};

verus! {

type IsoFns<In, Out> = (spec_fn(In) -> Out, spec_fn(Out) -> In);

pub trait Mapper {
    type In;

    type Out;

    spec fn spec_map(&self, i: Self::In) -> Self::Out;

    spec fn spec_map_rev(&self, o: Self::Out) -> Self::In;
}

impl<In, Out> Mapper for IsoFns<In, Out> {
    type In = In;

    type Out = Out;

    open spec fn spec_map(&self, i: In) -> Out {
        (self.0)(i)
    }

    open spec fn spec_map_rev(&self, o: Out) -> In {
        (self.1)(o)
    }
}

pub trait IsoMapper: Mapper {
    proof fn lemma_map_iso(&self, i: Self::In)
        ensures
            self.spec_map_rev(self.spec_map(i)) == i,
    ;

    proof fn lemma_map_iso_rev(&self, o: Self::Out)
        ensures
            self.spec_map(self.spec_map_rev(o)) == o,
    ;
}

impl<Inner, M> SpecType for super::Mapped<Inner, M> where
    Inner: SpecType,
    M: Mapper<In = Inner::Type>,
 {
    type Type = M::Out;

    open spec fn wf(&self, v: M::Out) -> bool {
        self.inner.wf(self.mapper.spec_map_rev(v))
    }
}

impl<Inner, M> SpecParser for super::Mapped<Inner, M> where
    Inner: SpecParser,
    M: Mapper<In = Inner::PT>,
 {
    type PT = M::Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, M::Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, self.mapper.spec_map(v))),
            None => None,
        }
    }
}

impl<Inner, M> GoodParser for super::Mapped<Inner, M> where
    Inner: GoodParser,
    M: IsoMapper<In = Inner::Type>,
 {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
        if let Some((n, inner_v)) = self.inner.spec_parse(ibuf) {
            self.mapper.lemma_map_iso(inner_v);
        }
    }
}

impl<Inner, M> SpecSerializerDps for super::Mapped<Inner, M> where
    Inner: SpecSerializerDps,
    M: Mapper<In = Inner::ST>,
 {
    type ST = M::Out;

    open spec fn spec_serialize_dps(&self, v: M::Out, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.mapper.spec_map_rev(v), obuf)
    }
}

impl<Inner, M> Serializability for super::Mapped<Inner, M> where
    Inner: Serializability,
    M: Mapper<In = Inner::ST>,
 {
    open spec fn serializable(&self, v: M::Out, obuf: Seq<u8>) -> bool {
        self.inner.serializable(self.mapper.spec_map_rev(v), obuf)
    }
}

impl<Inner, M> GoodSerializer for super::Mapped<Inner, M> where
    Inner: GoodSerializer,
    M: Mapper<In = Inner::ST>,
 {
    proof fn lemma_serialize_buf(&self, v: M::Out, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(self.mapper.spec_map_rev(v), obuf);
    }
}

impl<Inner, M> SpecSerializer for super::Mapped<Inner, M> where
    Inner: SpecSerializer,
    M: Mapper<In = Inner::ST>,
 {
    type ST = M::Out;

    open spec fn spec_serialize(&self, v: M::Out) -> Seq<u8> {
        self.inner.spec_serialize(self.mapper.spec_map_rev(v))
    }
}

impl<Inner: SpecParser, Out> SpecParser for super::Mapped<Inner, spec_fn(Inner::PT) -> Out> {
    type PT = Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, (self.mapper)(v))),
            None => None,
        }
    }
}

impl<Inner: SpecSerializerDps, Out> SpecSerializerDps for super::Mapped<
    Inner,
    spec_fn(Out) -> Inner::ST,
> {
    type ST = Out;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps((self.mapper)(v), obuf)
    }
}

impl<Inner: SpecSerializer, Out> SpecSerializer for super::Mapped<
    Inner,
    spec_fn(Out) -> Inner::ST,
> {
    type ST = Out;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        self.inner.spec_serialize((self.mapper)(v))
    }
}

} // verus!
