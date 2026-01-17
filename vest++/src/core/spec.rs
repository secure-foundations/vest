use vstd::prelude::*;

use crate::combinators::Either;

verus! {

/// The specification type (mathematical representation) of
/// a parsed/serialized value.
pub trait SpecType {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl SpecType for bool {

}

impl SpecType for u8 {

}

impl SpecType for u16 {

}

impl SpecType for u32 {

}

impl SpecType for u64 {

}

impl SpecType for usize {

}

impl SpecType for () {

}

impl<A: SpecType, B: SpecType> SpecType for (A, B) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf()
    }
}

impl<T: SpecType> SpecType for Option<T> {
    open spec fn wf(&self) -> bool {
        match self {
            Some(v) => v.wf(),
            None => true,
        }
    }
}

impl<A: SpecType, B: SpecType> SpecType for Either<A, B> {
    open spec fn wf(&self) -> bool {
        match self {
            Either::Left(v) => v.wf(),
            Either::Right(v) => v.wf(),
        }
    }
}

impl<T: SpecType> SpecType for Seq<T> {
    open spec fn wf(&self) -> bool {
        forall|i: int| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }
}

impl<T: SpecType, const N: usize> SpecType for [T; N] {
    open spec fn wf(&self) -> bool {
        forall|i: int| 0 <= i < N ==> #[trigger] self[i].wf()
    }
}

/// Used as the associated type for `Refined` combinator.
pub struct Subset<T, Pred> {
    pub val: T,
    pub pred: Pred,
}

pub type SpecPred<T> = spec_fn(T) -> bool;

impl<T: SpecType> SpecType for Subset<T, SpecPred<T>> {
    open spec fn wf(&self) -> bool {
        &&& self.val.wf()
        &&& (self.pred)(self.val)
    }
}

impl UniqueWfValue for () {
    proof fn lemma_unique_wf_value(&self, other: &Self) {
    }
}

/// A refinement of `SpecType` for types that have a unique well-formed value.
pub trait UniqueWfValue: SpecType {
    /// Lemma: if two values are both well-formed, they must be equal
    proof fn lemma_unique_wf_value(&self, other: &Self)
        ensures
            self.wf() && other.wf() ==> self == other,
    ;
}

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

/// A well-behaved serializer that satisfies key properties.
pub trait GoodSerializer: Serializability {
    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>)
        requires
            self.serializable(v, obuf),
        ensures
            v.wf() ==> exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf,
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
    GoodParser + GoodSerializer<ST = <Self as SpecParser>::PT>
{
}

#[verusfmt::skip]
impl<C> GoodCombinator for C where
    C:  GoodParser + GoodSerializer<ST = <Self as SpecParser>::PT>,
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
