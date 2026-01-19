use vstd::prelude::*;

use crate::combinators::Either;

verus! {

/// The specification type (mathematical representation) of
/// a parsed/serialized value.
pub trait SpecType {
    open spec fn wf(&self) -> bool {
        true
    }

    spec fn byte_len(&self) -> nat;
}

impl SpecType for bool {
    open spec fn byte_len(&self) -> nat {
        1
    }
}

impl SpecType for u8 {
    open spec fn byte_len(&self) -> nat {
        1
    }
}

impl SpecType for u16 {
    open spec fn byte_len(&self) -> nat {
        2
    }
}

impl SpecType for u32 {
    open spec fn byte_len(&self) -> nat {
        4
    }
}

impl SpecType for u64 {
    open spec fn byte_len(&self) -> nat {
        8
    }
}

impl SpecType for usize {
    open spec fn byte_len(&self) -> nat {
        8
    }
}

impl SpecType for () {
    open spec fn byte_len(&self) -> nat {
        0
    }
}

impl<A: SpecType, B: SpecType> SpecType for (A, B) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf()
    }
    open spec fn byte_len(&self) -> nat {
        self.0.byte_len() + self.1.byte_len()
    }
}

impl<T: SpecType> SpecType for Option<T> {
    open spec fn wf(&self) -> bool {
        match self {
            Some(v) => v.wf(),
            None => true,
        }
    }
    open spec fn byte_len(&self) -> nat {
        match self {
            Some(v) => v.byte_len(),
            None => 0,
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
    open spec fn byte_len(&self) -> nat {
        match self {
            Either::Left(v) => v.byte_len(),
            Either::Right(v) => v.byte_len(),
        }
    }
}

impl<T: SpecType> SpecType for Seq<T> {
    open spec fn wf(&self) -> bool {
        forall|i: int| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }
    open spec fn byte_len(&self) -> nat {
        self.fold_left(0, |acc: nat, elem: T| acc + elem.byte_len())
    }
}

impl<const N: usize> SpecType for [u8; N] {
    open spec fn byte_len(&self) -> nat {
        N as nat
    }
}

/// Used as the associated type for `Refined` combinator.
pub struct Subset<T, Pred> {
    pub val: T,
    pub pred: Pred,
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

impl<T: SpecType, Pred: SpecPred<T>> SpecType for Subset<T, Pred> {
    open spec fn wf(&self) -> bool {
        &&& self.val.wf()
        &&& self.pred.apply(self.val)
    }
    open spec fn byte_len(&self) -> nat {
        self.val.byte_len()
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

pub trait NonEmptyValue: SpecType {
    open spec fn non_empty(&self) -> bool {
        true
    }
    /// Lemma: a well-formed value has a positive byte length
    proof fn lemma_non_empty(&self)
        requires
            self.non_empty(),
        ensures
            self.wf() ==> self.byte_len() > 0,
    ;
}

impl NonEmptyValue for bool {
    proof fn lemma_non_empty(&self)
    {
    }
}

impl NonEmptyValue for u8 {
    proof fn lemma_non_empty(&self)
    {
    }
}

impl NonEmptyValue for u16 {
    proof fn lemma_non_empty(&self)
    {
    }
}

impl NonEmptyValue for u32 {
    proof fn lemma_non_empty(&self)
    {
    }
}

impl NonEmptyValue for u64 {
    proof fn lemma_non_empty(&self)
    {
    }
}

impl NonEmptyValue for usize {
    proof fn lemma_non_empty(&self)
    {
    }
}

impl<A, B> NonEmptyValue for (A, B) where A: SpecType, B: SpecType {
    open spec fn non_empty(&self) -> bool {
        self.0.byte_len() > 0 || self.1.byte_len() > 0
    }

    proof fn lemma_non_empty(&self)
    {
    }
}

impl<A, B> NonEmptyValue for Either<A, B> where A: SpecType, B: SpecType {
    open spec fn non_empty(&self) -> bool {
        self.byte_len() > 0
    }

    proof fn lemma_non_empty(&self)
    {
    }
}

impl<T: NonEmptyValue> NonEmptyValue for Option<T> {
    open spec fn non_empty(&self) -> bool {
        self matches Some(v) && v.non_empty()
    }

    proof fn lemma_non_empty(&self)
    {
        self->0.lemma_non_empty();
    }
}

impl<T: NonEmptyValue> NonEmptyValue for Seq<T> {
    open spec fn non_empty(&self) -> bool {
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].non_empty()
        &&& self.len() > 0
    }

    proof fn lemma_non_empty(&self)
    {
        if self.wf() {
            let last_index = (self.len() as int) - 1;
            self[last_index].lemma_non_empty();
        }
    }
}

impl<const N: usize> NonEmptyValue for [u8; N] {
    open spec fn non_empty(&self) -> bool {
        N > 0
    }

    proof fn lemma_non_empty(&self)
    {
    }
}

impl<T: NonEmptyValue, Pred: SpecPred<T>> NonEmptyValue for Subset<T, Pred> {
    open spec fn non_empty(&self) -> bool {
        self.val.non_empty()
    }

    proof fn lemma_non_empty(&self)
    {
        self.val.lemma_non_empty();
    }
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
pub trait GoodSerializer: SpecSerializerDps {
    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf,
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
