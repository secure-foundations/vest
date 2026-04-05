//! Mapper traits for type transformations used by [`super::Mapped`].
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// A bidirectional mapping between two types (forward for parsing, reverse for
/// serialization). For roundtrip guarantees, implement and prove
/// [`LossyMapper`] or [`LosslessMapper`] as appropriate.
pub trait Mapper {
    /// The input type.
    type In;

    /// The output type.
    type Out;

    /// Forward mapping (used during parsing).
    spec fn spec_map(&self, i: Self::In) -> Self::Out;

    /// Reverse mapping (used during serialization).
    spec fn spec_map_rev(&self, o: Self::Out) -> Self::In;

    /// Optional refinement predicates on the input type.
    ///
    /// This is the precondition for [`LosslessMapper::lemma_map_iso`].
    open spec fn wf_in(&self, i: Self::In) -> bool {
        true
    }

    /// Optional refinement predicates on the output type.
    ///
    /// This is the precondition for [`LossyMapper::lemma_map_iso_rev`].
    open spec fn wf_out(&self, o: Self::Out) -> bool {
        true
    }
}

/// A pair of spec functions forming a bidirectional mapping.
type MapFns<In, Out> = (spec_fn(In) -> Out, spec_fn(Out) -> In);

impl<In, Out> Mapper for MapFns<In, Out> {
    type In = In;

    type Out = Out;

    open spec fn spec_map(&self, i: In) -> Out {
        (self.0)(i)
    }

    open spec fn spec_map_rev(&self, o: Out) -> In {
        (self.1)(o)
    }
}

/// A [`Mapper`] that can be lossy (i.e., malleable).
pub trait LossyMapper: Mapper {
    /// A sound mapper should satisfy `spec_map(spec_map_rev(o)) == o` for all well-formed `o`.
    /// That is, once `Self::Out` values are mapped to `Self::In`, `spec_map` should map them back to the original `Self::Out` values.
    proof fn lemma_sound_mapper(&self, o: Self::Out)
        requires
            self.wf_out(o),
        ensures
            self.spec_map(self.spec_map_rev(o)) == o,
    ;
}

/// A [`Mapper`] that is lossless (i.e., non-malleable).
pub trait LosslessMapper: LossyMapper {
    /// A lossless mapper should satisfy `spec_map_rev(spec_map(i)) == i` for all well-formed `i`.
    /// That is, `spec_map` should be injective on well-formed `Self::In` values, and `spec_map_rev` should be its inverse.
    proof fn lemma_lossless_mapper(&self, i: Self::In)
        requires
            self.wf_in(i),
        ensures
            self.spec_map_rev(self.spec_map(i)) == i,
    ;

    /// For well-formed `i`, `spec_map(i)` should also be well-formed.
    proof fn lemma_mapper_wf_in_out(&self, i: Self::In)
        requires
            self.wf_in(i),
        ensures
            self.wf_out(self.spec_map(i)),
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

impl<Inner, M> SoundParser for super::Mapped<Inner, M> where
    Inner: SoundParser,
    M: LosslessMapper<In = Inner::PVal>,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.inner.sound_inv()
        &&& forall|v: Inner::T| self.inner.consistent(v) ==> self.mapper.wf_in(v)
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
        self.inner.lemma_parse_sound_value(ibuf);
        if let Some((_n, inner_v)) = self.inner.spec_parse(ibuf) {
            assert(self.mapper.wf_in(inner_v));
            self.mapper.lemma_lossless_mapper(inner_v);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
        if let Some((_n, inner_v)) = self.inner.spec_parse(ibuf) {
            assert(self.mapper.wf_in(inner_v));
            self.mapper.lemma_mapper_wf_in_out(inner_v);
            self.mapper.lemma_lossless_mapper(inner_v);
            assert(self.consistent(self.mapper.spec_map(inner_v)));
        }
    }
}

impl<Inner, M> Consistency for super::Mapped<Inner, M> where
    Inner: Consistency,
    M: Mapper<In = Inner::Val>,
 {
    type Val = M::Out;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.inner.consistent(self.mapper.spec_map_rev(v))
        &&& self.mapper.wf_out(v)
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

impl<Inner, M> Unambiguity for super::Mapped<Inner, M> where
    Inner: Unambiguity,
    M: Mapper<In = Inner::PVal>,
 {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<Inner, M> NonTailFmt for super::Mapped<Inner, M> where
    Inner: NonTailFmt,
    M: Mapper<In = Inner::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: M::Out, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(self.mapper.spec_map_rev(v), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: M::Out, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(self.mapper.spec_map_rev(v), obuf);
    }
}

impl<Inner, M> GoodSerializer for super::Mapped<Inner, M> where
    Inner: GoodSerializer,
    M: Mapper<In = Inner::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

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

impl<Inner: SpecParser, Out> SpecParser for super::Mapped<Inner, spec_fn(Inner::PVal) -> Out> {
    type PVal = Out;

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
    spec_fn(Out) -> Inner::SVal,
> {
    type SVal = Out;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize((self.mapper)(v))
    }
}

} // verus!
