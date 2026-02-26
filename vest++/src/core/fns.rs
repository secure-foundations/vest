//! Type aliases and trait implementations allowing plain `spec_fn`s to serve as combinators.

use crate::core::spec::{
    Consistency, GoodParser, PredFnSpec, SpecByteLen, SpecParser, SpecSerializer,
    SpecSerializerDps, Unambiguity,
};
use vstd::prelude::*;

verus! {

/// A spec-level function that computes the serialized byte length of a value.
pub type ByteLenFnSpec<T> = spec_fn(T) -> nat;

/// A spec-level parser function.
pub type ParserFnSpec<T> = spec_fn(Seq<u8>) -> Option<(int, T)>;

/// A spec-level serializer function in the "DPS" style.
pub type SerializerDPSFnSpec<T> = spec_fn(T, Seq<u8>) -> Seq<u8>;

/// A spec-level serializer function.
pub type SerializerFnSpec<T> = spec_fn(T) -> Seq<u8>;

impl<T> Consistency for PredFnSpec<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self)(v)
    }
}

impl<T> SpecByteLen for ByteLenFnSpec<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self)(v)
    }
}

impl<T> SpecParser for ParserFnSpec<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self)(ibuf)
    }
}

impl<T> SpecSerializerDps for SerializerDPSFnSpec<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self)(v, obuf)
    }
}

impl<T> SpecSerializer for SerializerFnSpec<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self)(v)
    }
}

/// A bundled DPS serializer: pairs a [`SerializerDPSFnSpec`] with a [`ByteLenFnSpec`].
pub type SerializerDPSSpecs<T> = (SerializerDPSFnSpec<T>, ByteLenFnSpec<T>);

impl<T> SpecByteLen for SerializerDPSSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1)(v)
    }
}

impl<T> SpecSerializerDps for SerializerDPSSpecs<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.0)(v, obuf)
    }
}

/// A bundled non-DPS serializer: pairs a [`SerializerFnSpec`] with a [`ByteLenFnSpec`].
pub type SerializerSpecs<T> = (SerializerFnSpec<T>, ByteLenFnSpec<T>);

impl<T> SpecByteLen for SerializerSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1)(v)
    }
}

impl<T> SpecSerializer for SerializerSpecs<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.0)(v)
    }
}

/// A spec-level unambiguity predicate.
pub type UnambiguityFnSpec = spec_fn() -> bool;

} // verus!
