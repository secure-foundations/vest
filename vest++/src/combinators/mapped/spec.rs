use crate::core::{proof::*, spec::*};
use vstd::{prelude::*, seq};

verus! {

type IsoFns<In, Out> = (spec_fn(In) -> Out, spec_fn(Out) -> In);

pub trait Mapper {
    type In: SpecType;

    type Out: SpecType;

    spec fn spec_map(&self, i: Self::In) -> Self::Out;

    spec fn spec_map_rev(&self, o: Self::Out) -> Self::In;
}

impl<In: SpecType, Out: SpecType> Mapper for IsoFns<In, Out> {
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
    proof fn lemma_map_wf(&self, v: Self::In)
        ensures
            v.wf() ==> self.spec_map(v).wf(),
    ;

    proof fn lemma_map_rev_wf(&self, v: Self::Out)
        ensures
            v.wf() ==> self.spec_map_rev(v).wf(),
    ;

    proof fn lemma_map_iso(&self, i: Self::In)
        ensures
            self.spec_map_rev(self.spec_map(i)) == i,
    ;

    proof fn lemma_map_iso_rev(&self, o: Self::Out)
        ensures
            self.spec_map(self.spec_map_rev(o)) == o,
    ;
}

impl<Inner, M> SpecParser for super::Mapped<Inner, M> where
    Inner: SpecParser,
    M: Mapper<In = Inner::PVal>,
 {
    type PVal = M::Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, M::Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, self.mapper.spec_map(v))),
            None => None,
        }
    }
}

impl<Inner, M> GoodParser for super::Mapped<Inner, M> where
    Inner: GoodParser,
    M: IsoMapper<In = Inner::PVal>,
 {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_wf(ibuf);
        if let Some((n, inner_v)) = self.inner.spec_parse(ibuf) {
            self.mapper.lemma_map_wf(inner_v);
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

impl<Inner, M> Unambiguity for super::Mapped<Inner, M> where
    Inner: Unambiguity,
    M: Mapper<In = Inner::ST>,
 {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<Inner, M> GoodSerializerDps for super::Mapped<Inner, M> where
    Inner: GoodSerializerDps,
    M: IsoMapper<In = Inner::ST>,
 {
    proof fn lemma_serialize_dps_buf(&self, v: M::Out, obuf: Seq<u8>) {
        self.mapper.lemma_map_rev_wf(v);
        self.inner.lemma_serialize_dps_buf(self.mapper.spec_map_rev(v), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: M::Out, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(self.mapper.spec_map_rev(v), obuf);
    }
}

impl<Inner, M> GoodSerializer for super::Mapped<Inner, M> where
    Inner: GoodSerializer,
    M: IsoMapper<In = Inner::SVal>,
 {
    proof fn lemma_serialize_len(&self, v: M::Out) {
        self.inner.lemma_serialize_len(self.mapper.spec_map_rev(v));
    }
}

impl<Inner, M> SpecByteLen for super::Mapped<Inner, M> where
    Inner: SpecByteLen,
    M: Mapper<In = Inner::T>,
 {
    type T = M::Out;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(self.mapper.spec_map_rev(v))
    }
}

impl<Inner, M> SpecSerializer for super::Mapped<Inner, M> where
    Inner: SpecSerializer,
    M: Mapper<In = Inner::SVal>,
 {
    type SVal = M::Out;

    open spec fn spec_serialize(&self, v: M::Out) -> Seq<u8> {
        self.inner.spec_serialize(self.mapper.spec_map_rev(v))
    }
}

impl<Inner: SpecParser, Out: SpecType> SpecParser for super::Mapped<
    Inner,
    spec_fn(Inner::PVal) -> Out,
> {
    type PVal = Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, (self.mapper)(v))),
            None => None,
        }
    }
}

impl<Inner: SpecSerializerDps, Out: SpecType> SpecSerializerDps for super::Mapped<
    Inner,
    spec_fn(Out) -> Inner::ST,
> {
    type ST = Out;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps((self.mapper)(v), obuf)
    }
}

impl<Inner: SpecSerializer, Out: SpecType> SpecSerializer for super::Mapped<
    Inner,
    spec_fn(Out) -> Inner::SVal,
> {
    type SVal = Out;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize((self.mapper)(v))
    }
}

} // verus!
