pub use super::types::*;
use vstd::prelude::*;

verus! {

/// Parser specification.
pub trait SpecParser {
    /// The type of parsed values.
    type PT: SpecType;

    /// Parser specification for values of [`Self::PT`].
    ///
    /// Returns `Some((n, v))` if parsing succeeds, where `n` is the number of bytes consumed
    /// from the input buffer `ibuf`, and `v` is the parsed value.
    /// Returns `None` if parsing fails.
    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)>;
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

pub trait SpecByteLen {
    type T: SpecType;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.blen()
    }
}

/// Serializer specification trait.
pub trait SpecSerializer {
    /// The type of values to be serialized.
    type ST: SpecType;

    /// Serializer specification for values of [`Self::ST`].
    ///
    /// Takes a value `v` and returns the serialized bytes.
    spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8>;
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

/// A well-behaved serializer that satisfies key properties.
pub trait GoodSerializerDps: SpecSerializerDps + SpecByteLen<T = Self::ST> {
    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf,
    ;

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>)
        ensures
            self.spec_serialize_dps(v, obuf).len() - obuf.len() == self.byte_len(v),
    ;
}

pub trait GoodSerializer: SpecSerializer + SpecByteLen<T = Self::ST> {
    /// Lemma: serializer produces buffer of the correct length
    proof fn lemma_serialize_len(&self, v: Self::ST)
        ensures
            self.spec_serialize(v).len() == self.byte_len(v),
    ;
}

/// Combined parser and serializer specification trait.
#[verusfmt::skip]
pub trait SpecCombinator:
    SpecParser +
    SpecSerializerDps<ST = <Self as SpecParser>::PT> +
    SpecSerializer<ST = <Self as SpecParser>::PT>
{
}

#[verusfmt::skip]
impl<T> SpecCombinator for T where
    T:  SpecParser +
        SpecSerializerDps<ST = <Self as SpecParser>::PT> +
        SpecSerializer<ST = <Self as SpecParser>::PT>,
{
}

/// Combined well-behaved parser and serializer trait.
#[verusfmt::skip]
pub trait GoodCombinator:
    GoodParser + GoodSerializerDps<ST = <Self as SpecParser>::PT>
{
}

#[verusfmt::skip]
impl<C> GoodCombinator for C where
    C:  GoodParser + GoodSerializerDps<ST = <Self as SpecParser>::PT>,
{
}

pub type WfSpecFn<T> = spec_fn(T) -> bool;

pub type ParserSpecFn<T> = spec_fn(Seq<u8>) -> Option<(int, T)>;

pub type SerializerDPSSpecFn<T> = spec_fn(T, Seq<u8>) -> Seq<u8>;

pub type SerializerSpecFn<T> = spec_fn(T) -> Seq<u8>;

pub type SerializableSpecFn<T> = spec_fn(T, Seq<u8>) -> bool;

impl<T: SpecType> SpecParser for ParserSpecFn<T> {
    type PT = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
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
    type ST = T;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        (self)(v)
    }
}

} // verus!
