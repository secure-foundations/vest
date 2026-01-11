use vstd::prelude::*;

verus! {

/// The specification type (mathematical representation) of
/// a parsed/serialized value.
pub trait SpecType {
    type Type;

    /// Well-formedness predicate for values of [`Self::Type`].
    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
}

/// A refinement of `SpecType` for types that have a unique well-formed value.
pub trait UniqueWfValue: SpecType {
    /// Lemma: if two values are both well-formed, they must be equal
    proof fn lemma_unique_wf_value(&self, v1: Self::Type, v2: Self::Type)
        ensures
            self.wf(v1) && self.wf(v2) ==> v1 == v2,
    ;
}

/// Parser specification.
pub trait SpecParser {
    /// The type of parsed values.
    type PT;

    /// Parser specification for values of [`Self::PT`].
    ///
    /// Returns `Some((n, v))` if parsing succeeds, where `n` is the number of bytes consumed
    /// from the input buffer `ibuf`, and `v` is the parsed value.
    /// Returns `None` if parsing fails.
    spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)>;
}

/// A well-behaved parser that satisfies key properties.
pub trait GoodParser: SpecType + SpecParser<PT = <Self as SpecType>::Type> {
    /// Lemma: parser returns valid buffer positions
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    ;

    /// Lemma: parser returns well-formed values
    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.wf(v),
    ;
}

/// Serializer specification trait (destination passing style).
pub trait SpecSerializerDps {
    /// The type of values to be serialized.
    type ST;

    /// Serializability constraint for values of [`Self::ST`] and output buffer.
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        true
    }

    /// Destination passing style serializer specification for values of [`Self::ST`].
    ///
    /// Takes a value `v` and an output buffer `obuf`, and returns the new output buffer
    /// after serializing `v` into it.
    spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8>;
}

/// Serializer specification trait.
pub trait SpecSerializer {
    /// The type of values to be serialized.
    type ST;

    /// Serializer specification for values of [`Self::ST`].
    ///
    /// Takes a value `v` and returns the serialized bytes.
    spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8>;
}

/// A well-behaved serializer that satisfies key properties.
pub trait GoodSerializer: SpecType + SpecSerializerDps<ST = <Self as SpecType>::Type> {
    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_buf(&self, v: <Self as SpecType>::Type, obuf: Seq<u8>)
        requires
            self.serializable(v, obuf),
        ensures
            self.wf(v) ==> exists|new_buf: Seq<u8>|
                self.spec_serialize_dps(v, obuf) == new_buf + obuf,
    ;
}

/// Combined parser and serializer specification trait.
pub trait SpecCombinator: SpecType + SpecParser<PT = <Self as SpecType>::Type> + SpecSerializerDps<
    ST = <Self as SpecType>::Type,
> + SpecSerializer<ST = <Self as SpecType>::Type> {

}

impl<T> SpecCombinator for T where
    T: SpecType + SpecParser<PT = <T as SpecType>::Type> + SpecSerializerDps<
        ST = <T as SpecType>::Type,
    > + SpecSerializer<ST = <T as SpecType>::Type>,
 {

}

/// Combined well-behaved parser and serializer trait.
pub trait GoodCombinator where
    Self: SpecType + SpecParser<PT = <Self as SpecType>::Type> + SpecSerializerDps<
        ST = <Self as SpecType>::Type,
    > + SpecSerializer<ST = <Self as SpecType>::Type> + GoodParser<
        PT = <Self as SpecType>::Type,
    > + GoodSerializer<ST = <Self as SpecType>::Type>,
 {

}

impl<C> GoodCombinator for C where
    C: SpecType + SpecParser<PT = <C as SpecType>::Type> + SpecSerializerDps<
        ST = <C as SpecType>::Type,
    > + SpecSerializer<ST = <C as SpecType>::Type> + GoodParser<
        PT = <C as SpecType>::Type,
    > + GoodSerializer<ST = <C as SpecType>::Type>,
 {

}

type ParserSpecFn<T> = spec_fn(Seq<u8>) -> Option<(int, T)>;

// type SerializerDPSSpecFn<T> = spec_fn(T, Seq<u8>) -> Seq<u8>;
// type SerializerSpecFn<T> = spec_fn(T) -> Seq<u8>;
// #[verifier::reject_recursive_types(T)]
// pub struct ParserFnSpec<T> {
//     pub parse_fn: ParserSpecFn<T>,
// }
impl<T> SpecParser for ParserSpecFn<T> {
    type PT = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        (self)(ibuf)
    }
}

pub enum NestedBracesT {
    Brace(Box<NestedBracesT>),
    Eps,
}

// type NestedBracesTInner = Either<Box<NestedBracesT>, ()>;
// spec fn nested_braces(
//     // p: PFn<NestedBracesT>,
//     // s: SFn<NestedBracesT>,
// ) -> Choice<Terminated<Preceded<Literal<1>, Callback<NestedBracesT>>, Literal<1>>, Empty> {
//     let p = |input, bound| p_nested_braces(input, bound);
//     Choice(
//         Terminated(Preceded(Literal([0x7B]), Callback(p)), Literal([0x7D])),
//         Empty,
//     )
// }
// Commented out example with recursive FnSpec parser - FnSpec doesn't implement SpecType
// spec fn p_nested_braces(input: Seq<u8>) -> Option<(int, NestedBracesT)>
//     decreases input.len()
// {
//     use crate::combinators::*;
//     let parse_fn = |rem: Seq<u8>| {
//         if rem.len() < input.len() {
//             p_nested_braces(rem)
//         } else {
//             None
//         }
//     };
//     match Choice(
//         Terminated(Preceded(Tag { inner: Fixed::<1>, tag: seq![0x7Bu8]}, parse_fn), Tag { inner: Fixed::<1>, tag: seq![0x7Du8]}),
//         Tag { inner: Fixed::<1>, tag: seq![0x00u8]},
//     ).spec_parse(input) {
//         Some((n, v)) => match v {
//             Either::Left(inner) => Some((n, (NestedBracesT::Brace(Box::new(inner))))),
//             Either::Right(_) => Some((n, NestedBracesT::Eps)),
//         },
//         None => None,
//     }
// }
} // verus!
