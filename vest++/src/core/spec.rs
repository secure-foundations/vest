use vstd::prelude::*;

verus! {

/// Parser specification.
pub trait SpecParser {
    /// The type of parsed values.
    type PVal;

    /// Parser specification for values of [`Self::PT`].
    ///
    /// Returns `Some((n, v))` if parsing succeeds, where `n` is the number of bytes consumed
    /// from the input buffer `ibuf`, and `v` is the parsed value.
    /// Returns `None` if parsing fails.
    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)>;
}

pub open spec fn disjoint_domains<P1: SpecParser, P2: SpecParser>(p1: P1, p2: P2) -> bool {
    forall|input: Seq<u8>| p1.spec_parse(input) is Some && p2.spec_parse(input) is Some ==> false
}

/// Combinator denotations that admit disjoint sets of values.
///
/// This is the necessary condition for [`crate::combinators::Alt`] to be non-malleable.
pub trait DisjointFrom<Other: Consistency<Val = Self::Val>>: Consistency {
    /// Lemma: the combinator [`Self`] and the combinator [`Other`] are disjoint if there is no value `v` that is consistent with both combinator denotations.
    proof fn lemma_disjoint(&self, other: &Other, v: Self::Val)
        ensures
            self.consistent(v) && other.consistent(v) ==> false,
    ;
}

pub open spec fn parser_fails_on<P: SpecParser>(p: P, ibuf: Seq<u8>) -> bool {
    p.spec_parse(ibuf) is None
}

/// A well-behaved parser that satisfies key properties.
pub trait GoodParser: SpecByteLen + SpecParser<PVal = Self::T> + Consistency<Val = Self::T> {
    /// Invariants for the parser specification [`SpecParser`] w.r.t.
    /// the consistency condition defined by [`Consistency`] as well as the
    /// byte length function defined by [`SpecByteLen`].
    ///
    /// This is primarily used for using functions as combinators. See [`crate::core::fns`] for more details.
    open spec fn inv(&self) -> bool {
        true
    }

    /// Lemma: parser returns valid buffer positions
    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>)
        requires
            self.inv(),
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    /// Lemma: parser returns the correct # of bytes consumed w.r.t. the value
    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>)
        requires
            self.inv(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> n == self.byte_len(v),
    ;

    /// Lemma: parser returns consistent values
    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>)
        requires
            self.inv(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.consistent(v),
    ;
}

/// Establish the consistency between the value and the combinator denotation.
///
/// ## Examples
///
/// - For a [`crate::combinators::Refined`] combinator, the consistency condition would be the refinement predicate.
/// - For a [`crate::combinators::Varied`] combinator, the consistency condition would be that the value's length is equal to `varied.0`.
pub trait Consistency {
    type Val;

    spec fn consistent(&self, v: Self::Val) -> bool;
}

/// Combinators whose consistency requirement admits at most one value.
///
/// This is used by combinators like [`crate::combinators::Preceded`] and
/// [`crate::combinators::Terminated`], where one component value is omitted.
pub trait AdmitsUniqueVal: Consistency {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val)
        ensures
            self.consistent(v1) && self.consistent(v2) ==> v1 == v2,
    ;
}

pub trait SpecPred<T> {
    spec fn apply(&self, value: T) -> bool;
}

pub type PredFnSpec<T> = spec_fn(T) -> bool;

impl<T> SpecPred<T> for PredFnSpec<T> {
    open spec fn apply(&self, value: T) -> bool {
        self(value)
    }
}

/// Serializer specification trait (destination passing style).
pub trait SpecSerializerDps {
    /// The type of values to be serialized.
    type ST;

    /// Destination passing style serializer specification for values of [`Self::ST`].
    ///
    /// Takes a value `v` and an output buffer `obuf`, and returns the new output buffer
    /// after serializing `v` into it.
    spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8>;
}

/// Denote the serialized byte length of values of [`Self::T`].
pub trait SpecByteLen {
    /// The type of values that can be serialized.
    type T;

    /// The byte length of [`Self::T`].
    spec fn byte_len(&self, v: Self::T) -> nat;
}

/// Encapsulate "bytes combinators".
pub trait BytesCombinator: SpecByteLen<T = Seq<u8>> {
    proof fn lemma_byte_len_is_buf_len(&self, buf: Seq<u8>)
        ensures
            self.byte_len(buf) == buf.len(),
    ;
}

/// Serializer specification trait.
pub trait SpecSerializer {
    /// The type of values to be serialized.
    type SVal;

    /// Serializer specification for values of [`Self::SVal`].
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
pub trait Unambiguity: SpecParser {
    /// Unambiguity constraint for composing combinators.
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

} // verus!
pub use crate::core::fns::{
    ByteLenFnSpec, ParserFnSpec, SerializerDPSFnSpec, SerializerDPSSpecs, SerializerFnSpec,
    SerializerSpecs, UnambiguityFnSpec,
};
