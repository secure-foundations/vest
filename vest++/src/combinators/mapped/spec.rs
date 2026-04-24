//! Mapper traits for type transformations used by [`super::Mapped`].
use crate::{
    combinators::refined::Refined,
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

pub trait SpecMap {
    type SpecI;

    type SpecO;

    open spec fn wf(&self, i: Self::SpecI) -> bool {
        true
    }

    spec fn spec_map(&self, i: Self::SpecI) -> Self::SpecO;
}

impl<I, O> SpecMap for spec_fn(I) -> O {
    type SpecI = I;

    type SpecO = O;

    open spec fn spec_map(&self, i: Self::SpecI) -> Self::SpecO {
        (self)(i)
    }
}

pub struct BiMap<M, MRev>(pub M, pub MRev);

impl<M, MRev> BiMap<M, MRev> where M: SpecMap, MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI> {
    pub open spec fn sound(&self, o: M::SpecO) -> bool
        recommends
            self.1.wf(o),
    {
        let BiMap(m, mrev) = *self;
        m.spec_map(mrev.spec_map(o)) == o
    }

    pub open spec fn lossless(&self, i: M::SpecI) -> bool
        recommends
            self.0.wf(i),
    {
        let BiMap(m, mrev) = *self;
        mrev.spec_map(m.spec_map(i)) == i
    }
}

impl<Inner, M, MRev> SpecParser for super::Map<Inner, BiMap<M, MRev>> where
    Inner: SpecParser,
    M: SpecMap<SpecI = Inner::PVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type PVal = M::SpecO;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, self.mapper.0.spec_map(v))),
            None => None,
        }
    }
}

impl<Inner, M, MRev> SafeParser for super::Map<Inner, BiMap<M, MRev>> where
    Inner: SafeParser,
    M: SpecMap<SpecI = Inner::PVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    open spec fn safe_inv(&self) -> bool {
        self.inner.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }
}

impl<Inner, M, MRev> SoundParser for super::Map<Inner, BiMap<M, MRev>> where
    Inner: SoundParser,
    M: SpecMap<SpecI = Inner::PVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.inner.sound_inv()
        &&& forall|i: Inner::T| #![auto] self.inner.consistent(i) ==> self.mapper.lossless(i)
        &&& forall|i: Inner::T|
            #![auto]
            self.inner.consistent(i) ==> self.mapper.1.wf(self.mapper.0.spec_map(i))
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
        self.inner.lemma_parse_sound_value(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<Inner, M, MRev> Consistency for super::Map<Inner, BiMap<M, MRev>> where
    Inner: Consistency,
    M: SpecMap<SpecI = Inner::Val>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type Val = M::SpecO;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.mapper.1.wf(v)
        &&& self.inner.consistent(self.mapper.1.spec_map(v))
    }
}

impl<Inner, M, MRev> SpecSerializerDps for super::Map<Inner, BiMap<M, MRev>> where
    Inner: SpecSerializerDps,
    M: SpecMap<SpecI = Inner::ST>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type ST = M::SpecO;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.mapper.1.spec_map(v), obuf)
    }
}

impl<Inner, M, MRev> NonTailFmt for super::Map<Inner, BiMap<M, MRev>> where
    Inner: NonTailFmt,
    M: SpecMap<SpecI = Inner::ST>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(self.mapper.1.spec_map(v), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(self.mapper.1.spec_map(v), obuf);
    }
}

impl<Inner, M, MRev> SpecSerializer for super::Map<Inner, BiMap<M, MRev>> where
    Inner: SpecSerializer,
    M: SpecMap<SpecI = Inner::SVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type SVal = M::SpecO;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(self.mapper.1.spec_map(v))
    }
}

impl<Inner, M, MRev> GoodSerializer for super::Map<Inner, BiMap<M, MRev>> where
    Inner: GoodSerializer,
    M: SpecMap<SpecI = Inner::SVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len(self.mapper.1.spec_map(v));
    }
}

impl<Inner, M, MRev> SpecByteLen for super::Map<Inner, BiMap<M, MRev>> where
    Inner: SpecByteLen,
    M: SpecMap<SpecI = Inner::T>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type T = M::SpecO;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(self.mapper.1.spec_map(v))
    }
}

impl<Inner, M, MRev> StaticByteLen for super::Map<Inner, BiMap<M, MRev>> where
    Inner: StaticByteLen,
    M: SpecMap<SpecI = Inner::T>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    open spec fn static_byte_len() -> nat {
        Inner::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_static_len_matches_byte_len(self.mapper.1.spec_map(v));
    }
}

/// A bidirectional mapping between two types (forward for parsing, reverse for
/// serialization). For roundtrip guarantees, implement and prove
/// [`LossyMapper`] or [`LosslessMapper`] as appropriate.
pub trait SpecMapper {
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
    /// This is the precondition for [`LosslessMapper::lemma_lossless_mapper`].
    open spec fn wf_in(&self, i: Self::In) -> bool {
        true
    }

    /// Optional refinement predicates on the output type.
    ///
    /// This is the precondition for [`LossyMapper::lemma_sound_mapper`].
    open spec fn wf_out(&self, o: Self::Out) -> bool {
        true
    }
}

/// A [`Mapper`] that can be lossy (i.e., malleable).
pub trait LossyMapper: SpecMapper {
    /// A sound mapper should satisfy `spec_map(spec_map_rev(o)) == o` for all well-formed `o`.
    /// That is, once `Self::Out` values are mapped to `Self::In`, `spec_map` should map them back to the original `Self::Out` values.
    proof fn lemma_sound_mapper(&self, o: Self::Out)
        requires
            self.wf_out(o),
        ensures
            self.spec_map(self.spec_map_rev(o)) == o,
    ;

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out)
        requires
            self.wf_out(o),
        ensures
            self.wf_in(self.spec_map_rev(o)),
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
    M: SpecMapper<In = Inner::PVal>,
 {
    type PVal = M::Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, M::Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, self.mapper.spec_map(v))),
            None => None,
        }
    }
}

impl<Inner, M> SafeParser for super::Mapped<Inner, M> where
    Inner: SafeParser,
    M: SpecMapper<In = Inner::PVal>,
 {
    open spec fn safe_inv(&self) -> bool {
        self.inner.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        assert(self.safe_inv());
        self.inner.lemma_parse_safe(ibuf);
    }
}

impl<Inner, M> SoundParser for super::Mapped<Inner, M> where
    Inner: SoundParser,
    M: LosslessMapper<In = Inner::PVal>,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.inner.sound_inv()
        &&& forall|v: Inner::T| #![auto] self.inner.consistent(v) ==> self.mapper.wf_in(v)
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
    M: SpecMapper<In = Inner::Val>,
 {
    type Val = M::Out;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.mapper.wf_out(v)
        &&& self.inner.consistent(self.mapper.spec_map_rev(v))
    }
}

impl<Inner, M> SpecSerializerDps for super::Mapped<Inner, M> where
    Inner: SpecSerializerDps,
    M: SpecMapper<In = Inner::ST>,
 {
    type ST = M::Out;

    open spec fn spec_serialize_dps(&self, v: M::Out, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.mapper.spec_map_rev(v), obuf)
    }
}

impl<Inner, M> NonTailFmt for super::Mapped<Inner, M> where
    Inner: NonTailFmt,
    M: SpecMapper<In = Inner::ST>,
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
    M: SpecMapper<In = Inner::SVal>,
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
    M: SpecMapper<In = Inner::T>,
 {
    type T = M::Out;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(self.mapper.spec_map_rev(v))
    }
}

impl<Inner, M> StaticByteLen for super::Mapped<Inner, M> where
    Inner: StaticByteLen,
    M: SpecMapper<In = Inner::T>,
 {
    open spec fn static_byte_len() -> nat {
        Inner::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_static_len_matches_byte_len(self.mapper.spec_map_rev(v));
    }
}

impl<Inner, M> SpecSerializer for super::Mapped<Inner, M> where
    Inner: SpecSerializer,
    M: SpecMapper<In = Inner::SVal>,
 {
    type SVal = M::Out;

    open spec fn spec_serialize(&self, v: M::Out) -> Seq<u8> {
        self.inner.spec_serialize(self.mapper.spec_map_rev(v))
    }
}

pub type FnSpecMapper<In, Out> = (spec_fn(In) -> Out, spec_fn(Out) -> In);

impl<Inner: SpecParser, Out> SpecParser for super::Mapped<Inner, spec_fn(Inner::PVal) -> Out> {
    type PVal = Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, (self.mapper)(v))),
            None => None,
        }
    }
}

impl<Inner: SpecParser, Out> SpecParser for super::Mapped<Inner, FnSpecMapper<Inner::PVal, Out>> {
    type PVal = Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Out)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) => Some((n, (self.mapper.0)(v))),
            None => None,
        }
    }
}

impl<Inner: SafeParser, Out> SafeParser for super::Mapped<Inner, FnSpecMapper<Inner::PVal, Out>> {
    open spec fn safe_inv(&self) -> bool {
        self.inner.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        assert(self.safe_inv());
        self.inner.lemma_parse_safe(ibuf);
    }
}

impl<Inner: SoundParser, Out> SoundParser for super::Mapped<Inner, FnSpecMapper<Inner::PVal, Out>> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.inner.sound_inv()
        &&& forall|v: Inner::T|
            #![auto]
            self.inner.consistent(v) ==> (self.mapper.1)((self.mapper.0)(v)) == v
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
        self.inner.lemma_parse_sound_value(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<Inner: Consistency, Out> Consistency for super::Mapped<Inner, FnSpecMapper<Inner::Val, Out>> {
    type Val = Out;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.inner.consistent((self.mapper.1)(v))
    }
}

impl<Inner: SpecByteLen, Out> SpecByteLen for super::Mapped<Inner, FnSpecMapper<Inner::T, Out>> {
    type T = Out;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len((self.mapper.1)(v))
    }
}

impl<Inner: StaticByteLen, Out> StaticByteLen for super::Mapped<
    Inner,
    FnSpecMapper<Inner::T, Out>,
> {
    open spec fn static_byte_len() -> nat {
        Inner::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_static_len_matches_byte_len((self.mapper.1)(v));
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

impl<Inner, Out> SpecSerializerDps for super::Mapped<Inner, FnSpecMapper<Inner::ST, Out>> where
    Inner: SpecSerializerDps,
 {
    type ST = Out;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps((self.mapper.1)(v), obuf)
    }
}

impl<Inner, Out> NonTailFmt for super::Mapped<Inner, FnSpecMapper<Inner::ST, Out>> where
    Inner: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend((self.mapper.1)(v), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len((self.mapper.1)(v), obuf);
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

impl<Inner, Out> SpecSerializer for super::Mapped<Inner, FnSpecMapper<Inner::SVal, Out>> where
    Inner: SpecSerializer,
 {
    type SVal = Out;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize((self.mapper.1)(v))
    }
}

impl<Inner, Out> GoodSerializer for super::Mapped<Inner, FnSpecMapper<Inner::SVal, Out>> where
    Inner: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len((self.mapper.1)(v));
    }
}

pub type TryMapPred<In> = PredFnSpec<In>;

pub type TryMapInner<Inner, M> = super::Mapped<
    Refined<Inner, TryMapPred<<M as SpecMapper>::In>>,
    M,
>;

impl<Inner, M: SpecMapper> super::TryMap<Inner, M> {
    pub open spec fn inner(&self) -> TryMapInner<Inner, M> {
        super::Mapped {
            inner: Refined { inner: self.inner, pred: |v: M::In| self.mapper.wf_in(v) },
            mapper: self.mapper,
        }
    }
}

impl<Inner, M> SpecParser for super::TryMap<Inner, M> where
    Inner: SpecParser,
    M: SpecMapper<In = Inner::PVal>,
 {
    type PVal = M::Out;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, M::Out)> {
        self.inner().spec_parse(ibuf)
    }
}

impl<Inner, M> SafeParser for super::TryMap<Inner, M> where
    Inner: SafeParser,
    M: SpecMapper<In = Inner::PVal>,
 {
    open spec fn safe_inv(&self) -> bool {
        self.inner().safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner().lemma_parse_safe(ibuf);
    }
}

impl<Inner, M> SoundParser for super::TryMap<Inner, M> where
    Inner: SoundParser,
    M: LosslessMapper<In = Inner::PVal>,
 {
    open spec fn sound_inv(&self) -> bool {
        self.inner().sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner().lemma_parse_sound_value(ibuf);
    }
}

impl<Inner, M> Consistency for super::TryMap<Inner, M> where
    Inner: Consistency,
    M: SpecMapper<In = Inner::Val>,
 {
    type Val = M::Out;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.inner().consistent(v)
    }
}

impl<Inner, M> SpecSerializerDps for super::TryMap<Inner, M> where
    Inner: SpecSerializerDps,
    M: SpecMapper<In = Inner::ST>,
 {
    type ST = M::Out;

    open spec fn spec_serialize_dps(&self, v: M::Out, obuf: Seq<u8>) -> Seq<u8> {
        self.inner().spec_serialize_dps(v, obuf)
    }
}

impl<Inner, M> NonTailFmt for super::TryMap<Inner, M> where
    Inner: NonTailFmt,
    M: SpecMapper<In = Inner::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner().serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: M::Out, obuf: Seq<u8>) {
        self.inner().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: M::Out, obuf: Seq<u8>) {
        self.inner().lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner, M> GoodSerializer for super::TryMap<Inner, M> where
    Inner: GoodSerializer,
    M: SpecMapper<In = Inner::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        self.inner().serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: M::Out) {
        self.inner().lemma_serialize_len(v);
    }
}

impl<Inner, M> SpecByteLen for super::TryMap<Inner, M> where
    Inner: SpecByteLen,
    M: SpecMapper<In = Inner::T>,
 {
    type T = M::Out;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner().byte_len(v)
    }
}

impl<Inner, M> StaticByteLen for super::TryMap<Inner, M> where
    Inner: StaticByteLen,
    M: SpecMapper<In = Inner::T>,
 {
    open spec fn static_byte_len() -> nat {
        TryMapInner::<Inner, M>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner().lemma_static_len_matches_byte_len(v);
    }
}

impl<Inner, M> SpecSerializer for super::TryMap<Inner, M> where
    Inner: SpecSerializer,
    M: SpecMapper<In = Inner::SVal>,
 {
    type SVal = M::Out;

    open spec fn spec_serialize(&self, v: M::Out) -> Seq<u8> {
        self.inner().spec_serialize(v)
    }
}

} // verus!
