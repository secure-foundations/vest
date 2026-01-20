pub use super::types::*;
use vstd::prelude::*;

verus! {

/// Parser specification.
pub trait SpecParser {
    /// The type of parsed values.
    type PVal: SpecType;

    /// Parser specification for values of [`Self::PT`].
    ///
    /// Returns `Some((n, v))` if parsing succeeds, where `n` is the number of bytes consumed
    /// from the input buffer `ibuf`, and `v` is the parsed value.
    /// Returns `None` if parsing fails.
    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)>;
}

pub open spec fn parser_fails_on<P: SpecParser>(p: P, ibuf: Seq<u8>) -> bool {
    p.spec_parse(ibuf) is None
}

/// A well-behaved parser that satisfies key properties.
pub trait GoodParser: SpecParser {
    /// Lemma: parser returns valid buffer positions
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    /// Lemma: parser returns well-formed values
    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> v.wf(),
    ;
}

/// Serializer specification trait (destination passing style).
pub trait SpecSerializerDps {
    /// The type of values to be serialized.
    type ST: SpecType;

    /// Destination passing style serializer specification for values of [`Self::ST`].
    ///
    /// Takes a value `v` and an output buffer `obuf`, and returns the new output buffer
    /// after serializing `v` into it.
    spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8>;
}

/// Denote the serialized byte length of values of [`Self::T`].
pub trait SpecByteLen {
    /// The type of values that can be serialized.
    type T: SpecType;

    /// The byte length of values of [`Self::T`].
    ///
    /// The default implementation simply uses the `blen` method of [`Self::T`].
    /// All primitive combinators use this default implementation.
    ///
    /// This method is needed primarily because combinators that omit parsed values (like [`crate::combinators::Preceded`],
    ///  [`crate::combinators::Terminated`], and [`crate::combinators::Tag`])
    /// may not have a meaningful byte length just from [`Self::T`].
    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.blen()
    }
}

/// Serializer specification trait.
pub trait SpecSerializer {
    /// The type of values to be serialized.
    type SVal: SpecType;

    /// Serializer specification for values of [`Self::ST`].
    ///
    /// Takes a value `v` and returns the serialized bytes.
    spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8>;
}

/// Constraints imposed by combinators on the serializability of values.
pub trait Serializability: SpecSerializerDps {
    /// Serializability constraint for values of [`Self::ST`] and output buffer.
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        true
    }
}

/// Conditions for unambiguously composing formats.
/// This is meant to be an smt-friendlier version of [`Serializability`]
pub trait Unambiguity: SpecSerializerDps {
    /// Unambiguity constraint for serializer combinators.
    open spec fn unambiguous(&self) -> bool {
        true
    }
}

/// A well-behaved DPS serializer that satisfies key properties.
pub trait GoodSerializerDps: SpecByteLen + SpecSerializerDps<ST = Self::T> {
    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf,
    ;

    /// Lemma: serializer produces buffer of the correct length
    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>)
        ensures
            self.spec_serialize_dps(v, obuf).len() - obuf.len() == self.byte_len(v),
    ;
}

/// A well-behaved serializer that satisfies key properties.
pub trait GoodSerializer: SpecByteLen + SpecSerializer<SVal = Self::T> {
    /// Lemma: serializer produces buffer of the correct length
    proof fn lemma_serialize_len(&self, v: Self::SVal)
        ensures
            self.spec_serialize(v).len() == self.byte_len(v),
    ;
}

/// Combined parser and serializer specification trait.
#[verusfmt::skip]
pub trait SpecCombinator:
    SpecByteLen +
    SpecParser<PVal = Self::T> +
    SpecSerializer<SVal = Self::T> +
    SpecSerializerDps<ST = Self::T>
{
}

#[verusfmt::skip]
impl<T> SpecCombinator for T where
    T:  SpecByteLen +
        SpecParser<PVal = Self::T> +
        SpecSerializer<SVal = Self::T> +
        SpecSerializerDps<ST = Self::T>
{
}

pub type WfSpecFn<T> = spec_fn(T) -> bool;

pub type ParserSpecFn<T> = spec_fn(Seq<u8>) -> Option<(int, T)>;

pub type SerializerDPSSpecFn<T> = spec_fn(T, Seq<u8>) -> Seq<u8>;

pub type SerializerSpecFn<T> = spec_fn(T) -> Seq<u8>;

pub type SerializableSpecFn<T> = spec_fn(T, Seq<u8>) -> bool;

impl<T: SpecType> SpecParser for ParserSpecFn<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self)(ibuf)
    }
}

impl<T: SpecType> SpecSerializerDps for SerializerDPSSpecFn<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self)(v, obuf)
    }
}

impl<T: SpecType> SpecSerializer for SerializerSpecFn<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self)(v)
    }
}

} // verus!
