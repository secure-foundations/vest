pub use crate::buf_traits::*;
pub use crate::errors::*;
use alloc::boxed::Box;

use vstd::prelude::*;
use vstd::*;

verus! {

/// The parse result of a combinator.
pub type PResult<T, E> = Result<(usize, T), E>;

/// The serialize result of a combinator.
pub type SResult<T, E> = Result<T, E>;

/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type Type;

    /// Well-formedness of the format [`Self::type`] (e.g., refinements on the type).
    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }

    /// Pre-conditions for parsing and serialization.
    ///
    /// ## Examples
    ///
    /// - Sequencing combinators require that the first combinator is prefix-secure.
    /// - Repetition combinators require that the inner combinator is prefix-secure.
    /// - [`crate::regular::repetition::Repeat`] combinator requires that the
    ///   inner combinator is productive.
    /// - [`crate::regular::variant::Choice`] combinator requires that `Snd` is [`crate::regular::disjoint::DisjointFrom`] `Fst`.
    open spec fn requires(&self) -> bool {
        true
    }

    /// The specification of [`Combinator::parse`].
    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

    /// The specification of [`Combinator::serialize`].
    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;
}

/// Theorems and lemmas that must be proven for a combinator to be considered correct and secure.
pub trait SecureSpecCombinator: SpecCombinator {
    /// One of the top-level roundtrip properties
    /// It reads "if we serialize a (well-formed) value, then parsing the serialized bytes should
    /// give us the same value back."
    /// If we somehow get a different value, it means that different high-level values can
    /// correspond to the same low-level representation, or put differently, the same byte
    /// sequences can be parsed into different values.
    ///
    /// This property can be understood as
    /// 1. injectivity of serialization: different values should serialize to different byte
    ///    sequences
    /// 2. surjectivity of parsing: every valid high-level value should associate with at least one
    ///    low-level representation.
    /// 3. correctness of parsing: given a correct serializer that produces some byte sequence from
    ///   a value, the corresponding parser should be able to parse the byte sequence back to the
    ///   same value (can lead to format-confusion attacks if not satisfied).
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v) ==> self.spec_parse(self.spec_serialize(v)) == Some(
                (self.spec_serialize(v).len() as int, v),
            ),
    ;

    /// Followed from `theorem_serialize_parse_roundtrip`
    proof fn corollary_parse_surjective(&self, v: Self::Type)
        requires
            self.requires(),
            self.wf(v),
        ensures
            exists|b: Seq<u8>| #[trigger] self.spec_parse(b) matches Some((_, v_)) && v_ == v,
    {
        self.theorem_serialize_parse_roundtrip(v);
    }

    /// Followed from `theorem_serialize_parse_roundtrip`
    proof fn corollary_serialize_injective(&self, v1: Self::Type, v2: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v1) && self.wf(v2) ==> self.spec_serialize(v1) == self.spec_serialize(v2) ==> v1
                == v2,
    {
        self.theorem_serialize_parse_roundtrip(v1);
        self.theorem_serialize_parse_roundtrip(v2);
    }

    /// Followed from `theorem_serialize_parse_roundtrip`
    proof fn corollary_serialize_injective_contraposition(&self, v1: Self::Type, v2: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v1) && self.wf(v2) ==> v1 != v2 ==> self.spec_serialize(v1)
                != self.spec_serialize(v2),
    {
        self.theorem_serialize_parse_roundtrip(v1);
        self.theorem_serialize_parse_roundtrip(v2);
    }

    /// One of the top-level roundtrip properties
    /// It reads "if we successfully parse a byte sequence, then serializing the parsed value should
    /// give us the same byte sequence back."
    /// If we somehow get a different byte sequence, it means that different low-level representations
    /// can correspond to the same high-level value, or put differently, the same value can be
    /// serialized into different byte sequences.
    ///
    /// This property can be understood as
    /// 1. injectivity of parsing: different byte sequences should parse to different values (can
    ///    lead to parser mallability attacks if not satisfied)
    /// 2. correctness of serialization: given a correct parser that produces some value from a byte
    ///   sequence, the corresponding serializer should be able to serialize the value back to the same
    ///   byte sequence (up to the number of bytes consumed).
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(buf) matches Some((n, v)) ==> {
                &&& self.wf(v)
                &&& self.spec_serialize(v) == buf.take(n)
            },
    ;

    /// Followed from `theorem_parse_serialize_roundtrip`
    proof fn corollary_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==> self.spec_parse(buf2) matches Some(
                (n2, v2),
            ) ==> v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    {
        self.theorem_parse_serialize_roundtrip(buf1);
        self.theorem_parse_serialize_roundtrip(buf2);
    }

    /// Like an associated constant, denotes whether the combinator is prefix-secure.
    spec fn is_prefix_secure() -> bool;

    /// This prefix-secure lemma is used in the proof of the roundtrip properties for sequencing
    /// and repeating combinators.
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        requires
            self.requires(),
        ensures
            Self::is_prefix_secure() ==> self.spec_parse(s1) is Some ==> self.spec_parse(s1 + s2)
                == self.spec_parse(s1),
    ;

    /// The parser-length lemma is used in the proof of the roundtrip properties and the prefix-secure
    /// lemma
    proof fn lemma_parse_length(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(s) matches Some((n, _)) ==> 0 <= n <= s.len(),
    ;

    /// Like an associated constant, denotes whether the combinator is productive
    spec fn is_productive(&self) -> bool;

    /// This lemma is used in the proof of the roundtrip properties for optional and unbounded
    /// repeating combinators.
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.is_productive() ==> (self.spec_parse(s) matches Some((n, _)) ==> n > 0),
    ;

    /// This lemma is used in the proof of the roundtrip properties for optional and unbounded
    /// repeating combinators.
    proof fn lemma_serialize_productive(&self, v: Self::Type)
        requires
            self.requires(),
            self.wf(v),
        ensures
            self.is_productive() ==> self.spec_serialize(v).len() > 0,
    {
        self.theorem_serialize_parse_roundtrip(v);
        self.lemma_parse_productive(self.spec_serialize(v));
    }
}

/// Implementation for parser and serializer combinators. A combinator's view must be a
/// [`SecureSpecCombinator`].
pub trait Combinator<'x, I, O>: View where
    I: VestInput,
    O: VestOutput<I>,
    Self::V: SecureSpecCombinator<Type = <Self::Type as View>::V>,
 {
    /// The result type of parsing
    type Type: View;

    /// The input type of serialization, often a reference to [`Self::Type`].
    /// For "structural" formats though (e.g., [`crate::regular::sequence::Pair`] and [`crate::regular::variant::Choice`]),
    /// this is the tuple/sum of the corresponding [`Combinator::SType`] types.
    type SType: View<V = <Self::Type as View>::V>;

    /// The length of the output buffer.
    /// This can be used to optimize serialization by pre-allocating the buffer.
    fn length(&self, v: Self::SType) -> (len: usize)
        requires
            self@.requires(),
            self.ex_requires(),
            self@.wf(v@),
            self@.spec_serialize(v@).len() <= usize::MAX,
        ensures
            len == self@.spec_serialize(v@).len(),
    ;

    /// Additional pre-conditions for parsing and serialization
    ///
    /// e.g., [`crate::regular::sequence::Pair`] combinator requires that the
    ///   [`crate::regular::sequence::Continuation`] is well-formed w.r.t. the
    ///   `spec_fn` closure.
    open spec fn ex_requires(&self) -> bool {
        true
    }

    /// The parsing function.
    /// To enable "zero-copy" parsing, implementations of `parse` should not
    /// consume/deepcopy the input buffer `I`, but rather return a slice of the
    /// input buffer for `Self::Type` whenever possible.
    /// See [`crate::buf_traits::VestInput`] and [`crate::buf_traits::VestPublicInput`] for
    /// more details.
    ///
    /// ## Pre-conditions
    ///
    /// - [`SpecCombinator::requires`]
    /// - [`Combinator::ex_requires`]
    ///
    /// ## Post-conditions
    /// Essentially, the implementation of `parse` is functionally correct with respect to the
    /// specification `spec_parse` on both success and failure cases.
    fn parse(&self, s: I) -> (res: PResult<Self::Type, ParseError>)
        requires
            self@.requires(),
            self.ex_requires(),
            s@.len() <= usize::MAX,
        ensures
            res matches Ok((n, v)) ==> self@.spec_parse(s@) == Some((n as int, v@)),
            self@.spec_parse(s@) matches Some((n, v)) ==> res matches Ok((m, u)) && m == n && v
                == u@,
            res is Err ==> self@.spec_parse(s@) is None,
            self@.spec_parse(s@) is None ==> res is Err,
    ;

    /// The serialization function.
    /// The intended use of `serialize` is to serialize a value `v` into the
    /// buffer `buf` at the position `pos` "in-place" (i.e., without
    /// allocating a new buffer or extending the buffer).
    ///
    /// ## Pre-conditions
    ///
    /// - [`SpecCombinator::requires`]
    /// - [`Combinator::ex_requires`]
    /// - [`SpecCombinator::wf`]
    /// - `pos` is less than or equal to the length of the buffer, whose length
    ///   is less than or equal to `usize::MAX`.
    ///
    /// ## Post-conditions
    /// `serialize` ensures that it is functionally correct with respect to the
    /// specification `spec_serialize` when it returns `Ok`. This is because
    /// `serialize` being a partial function can fail (e.g.,
    /// insufficient buffer space), while `spec_serialize` is a
    /// total function (with infinite buffer size) and will never fail.
    fn serialize(&self, v: Self::SType, buf: &mut O, pos: usize) -> (res: SResult<
        usize,
        SerializeError,
    >)
        requires
            self@.requires(),
            self.ex_requires(),
            self@.wf(v@),
            pos <= old(buf)@.len() <= usize::MAX,
        ensures
            res matches Ok(n) ==> {
                &&& buf@.len() == old(buf)@.len()
                &&& pos <= usize::MAX - n && pos + n <= buf@.len()
                &&& n == self@.spec_serialize(v@).len()
                &&& buf@ == seq_splice(old(buf)@, pos, self@.spec_serialize(v@))
            },
    ;
}

impl<C: SpecCombinator> SpecCombinator for &C {
    type Type = C::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        (*self).wf(v)
    }

    open spec fn requires(&self) -> bool {
        (*self).requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        (*self).spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (*self).spec_serialize(v)
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for &C {
    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        (*self).is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        (*self).theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (*self).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        (*self).lemma_prefix_secure(s1, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        (*self).lemma_parse_length(s)
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        (*self).lemma_parse_productive(s)
    }
}

impl<'x, I, O, C: Combinator<'x, I, O>> Combinator<'x, I, O> for &C where
    I: VestInput,
    O: VestOutput<I>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
 {
    type Type = C::Type;

    type SType = C::SType;

    fn length(&self, v: Self::SType) -> usize {
        assert(self.ex_requires());
        (*self).length(v)
    }

    open spec fn ex_requires(&self) -> bool {
        (*self).ex_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        (*self).parse(s)
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        (*self).serialize(v, data, pos)
    }
}

impl<C: SpecCombinator> SpecCombinator for Box<C> {
    type Type = C::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        (**self).wf(v)
    }

    open spec fn requires(&self) -> bool {
        (**self).requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        (**self).spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (**self).spec_serialize(v)
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for Box<C> {
    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        (**self).is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        (**self).theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (**self).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        (**self).lemma_prefix_secure(s1, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        (**self).lemma_parse_length(s)
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        (**self).lemma_parse_productive(s)
    }
}

impl<'x, I, O, C: Combinator<'x, I, O>> Combinator<'x, I, O> for Box<C> where
    I: VestInput,
    O: VestOutput<I>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
 {
    type Type = C::Type;

    type SType = C::SType;

    fn length(&self, v: Self::SType) -> usize {
        (**self).length(v)
    }

    open spec fn ex_requires(&self) -> bool {
        (**self).ex_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        (**self).parse(s)
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        (**self).serialize(v, data, pos)
    }
}

// The following is an attempt to support `Fn`s as combinators.
// I started implementing it because Verus doesn't support existential types (impl Trait) yet,
// which is required to be able to put `Depend` combinator in the function's return type,
// but more generally, I think it's probably also good to have a way in our framework to define
// combinators as a group of (parsing and serializing) functions.
//
// Overall this is doable, but it's a bit tricky to implement because of the current limitations of Verus:
// - Verus doesn't have general support for struct invariants yet, which means we have to add
// pre-conditions to the security properties (i.e. the struct containing a pair of parsing and
// serializing functions must be "well-formed" in some sense).
// - Verus doesn't have general support for `&mut` types yet, which means for serialization we
// cannot freely pass around the `&mut Vec<u8>`
//
// In theory, we could factor out all the lifetime parameters in `Combinator` trait and use generic
// type parameters instead for both parsing and serialization, but that would require another
// entire-codebase refactoring, which I think is not worth it at this point.
//
// #[verifier::reject_recursive_types(Type)]
// pub struct SpecCombinatorFn<Type, const Prefix: u8> {
//     pub parse: spec_fn(Seq<u8>) -> PResult<Type, ()>,
//     pub serialize: spec_fn(Type) -> SResult<Seq<u8>, ()>,
// }
//
// impl<Type, const Prefix: u8> SpecCombinatorFn<Type, Prefix> {
//     pub open spec fn new(
//         parse: spec_fn(Seq<u8>) -> PResult<Type, ()>,
//         serialize: spec_fn(Type) -> SResult<Seq<u8>, ()>,
//     ) -> (o: Self)
//         recommends
//             forall|v| Self::theorem_serialize_parse_roundtrip(parse, serialize, v),
//             forall|buf| Self::theorem_parse_serialize_roundtrip(parse, serialize, buf),
//             forall|s1, s2| Self::lemma_prefix_secure(parse, s1, s2),
//     {
//         Self { parse, serialize }
//     }
//
//     pub open spec fn theorem_serialize_parse_roundtrip(
//         parse: spec_fn(Seq<u8>) -> PResult<Type, ()>,
//         serialize: spec_fn(Type) -> SResult<Seq<u8>, ()>,
//         v: Type,
//     ) -> bool {
//         serialize(v) matches Ok(b) ==> parse(b) == Ok::<_, ()>((b.len() as usize, v))
//     }
//
//     pub open spec fn theorem_parse_serialize_roundtrip(
//         parse: spec_fn(Seq<u8>) -> Result<(usize, Type), ()>,
//         serialize: spec_fn(Type) -> Result<Seq<u8>, ()>,
//         buf: Seq<u8>,
//     ) -> bool {
//         buf.len() <= usize::MAX ==> ( parse(buf) matches Ok((n, v)) ==> serialize(v) == Ok::<
//         _,
//         (),
//         >(buf.take(n as int)) )
//     }
//
//     pub open spec fn lemma_prefix_secure(
//         parse: spec_fn(Seq<u8>) -> Result<(usize, Type), ()>,
//         s1: Seq<u8>,
//         s2: Seq<u8>,
//     ) -> bool {
//         s1.len() + s2.len() <= usize::MAX && (Prefix == 1) ==>
//         parse(s1) is Ok ==> parse(s1 + s2) == parse(s1)
//     }
// }
//
//
// impl<Type, const Prefix: u8> SpecCombinator for SpecCombinatorFn<Type, Prefix> {
//     type Type = Type;
//
//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
//         if let Ok((n, v)) = (self.parse)(s) {
//             if n <= s.len() {
//                 Ok((n, v))
//             } else {
//                 Err(())
//             }
//         } else {
//             Err(())
//         }
//     }
//
//     open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
//         (self.serialize)(v)
//     }
//
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//     }
// }
//
// impl<Type, const Prefix: u8> SecureSpecCombinator for SpecCombinatorFn<Type, Prefix> {
//     open spec fn is_prefix_secure() -> bool {
//         Prefix == 1
//     }
//
//     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
//         assume(Self::theorem_serialize_parse_roundtrip(self.parse, self.serialize, v));
//     }
//
//     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
//         assume(Self::theorem_parse_serialize_roundtrip(self.parse, self.serialize, buf));
//     }
//
//     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
//         assume(Self::lemma_prefix_secure(self.parse, s1, s2));
//     }
// }
//
// pub struct CombinatorFn<I, O, R, P, S, const Prefix: u8> where
//     I: VestInput,
//     O: VestOutput<I>,
//     R: View,
//     P: Continuation<I, Output = PResult<R, ParseError>>,
//     S: for<'a> Continuation<(R, &'a mut O, usize), Output = SResult<usize, SerializeError>>,
// {
//     pub parse: P,
//     pub serialize: S,
//     pub spec_parse: Ghost<spec_fn(Seq<u8>) -> PResult<R::V, ()>>,
//     pub spec_serialize: Ghost<spec_fn(R::V) -> SResult<Seq<u8>, ()>>,
//     phantom: std::marker::PhantomData<(I, O)>,
// }
//
// impl<'a, 'b, R, P, S, const Prefix: u8> View for CombinatorFn<'a, 'b, R, P, S, Prefix> where
//     R: View,
//     P: Fn(&'a [u8]) -> Result<(usize, R), ()>,
//     S: Fn(R, &'b mut Vec<u8>, usize) -> Result<usize, ()>,
// {
//     type V = SpecCombinatorFn<R::V, Prefix>;
//
//     open spec fn view(&self) -> Self::V {
//         let Ghost(parse) = self.spec_parse;
//         let Ghost(serialize) = self.spec_serialize;
//         SpecCombinatorFn {
//             parse,
//             serialize,
//         }
//     }
// }
//
// impl<'a, 'b, R, P, S, const Prefix: u8> Combinator for CombinatorFn<'a, 'b, R, P, S, Prefix> where
//     R: View,
//     P: Fn(&'a [u8]) -> Result<(usize, R), ()>,
//     S: Fn(R, &'b mut Vec<u8>, usize) -> Result<usize, ()>,
//     Self::V: SecureSpecCombinator<Type = R::V>,
//  {
//     type Result<'c> = R;
//
//     type Owned = R;
//
//     open spec fn spec_length(&self) -> Option<usize> {
//         None
//     }
//
//     fn length(&self) -> Option<usize> {
//         None
//     }
//
//     fn exec_is_prefix_secure() -> bool {
//         Prefix == 1
//     }
//
//     fn parse<'c>(&self, s: &'c [u8]) -> Result<(usize, Self::Result<'c>), ()> where 'c: 'a {
//         (self.parse)(s)
//     }
//
//     fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<usize, ()> {
//         (self.serialize)(v, data, pos)
//     }
// }
} // verus!
// ///////// Separating the parsing and serializing functions
// ///////// Unsuccesful due to conflicting trait impls and Verus limitations (&mut support)
// // pub trait Parser<I, O>
// // where
// //     I: VestInput,
// // {
// //     type Type;
// //
// //     fn parse_fn(&self, s: I) -> PResult<Self::Type, ParseError>;
// // }
// //
// // pub trait Serializer<I, O>
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// // {
// //     type Type;
// //
// //     fn serialize_fn(
// //         &self,
// //         v: Self::Type,
// //         data: &mut O,
// //         pos: usize,
// //     ) -> SResult<usize, SerializeError>;
// // }
// //
// // impl<I, O, Type, F> Parser<I, O> for F
// // where
// //     I: VestInput,
// //     F: Fn(I) -> PResult<Type, ParseError>,
// // {
// //     type Type = Type;
// //
// //     fn parse_fn(&self, s: I) -> PResult<Self::Type, ParseError> {
// //         self(s)
// //     }
// // }
// //
// // impl<I, O, Fst, Snd> Parser<I, O> for (Fst, Snd)
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// //     Fst: Combinator<I, O>,
// //     Snd: Combinator<I, O>,
// //     Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
// //     Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
// // {
// //     type Type = (Fst::Type, Snd::Type);
// //
// //     fn parse_fn(&self, s: I) -> PResult<Self::Type, ParseError> {
// //         (&self.0, &self.1).parse(s)
// //     }
// // }
// //
// // impl<I: VestPublicInput, O: VestPublicOutput<I>> Parser<I, O> for crate::regular::uints::U8 {
// //     type Type = u8;
// //
// //     fn parse_fn(&self, s: I) -> PResult<Self::Type, ParseError> {
// //         <_ as Combinator<I, O>>::parse(self, s)
// //     }
// // }
// //
// // fn parse_pair_of_u8<I, O>(s: I) -> PResult<(u8, u8), ParseError>
// // where
// //     I: VestPublicInput,
// //     O: VestPublicOutput<I>,
// // {
// //     <_ as Parser<I, O>>::parse_fn(&(crate::regular::uints::U8, crate::regular::uints::U8), s)
// // }
// //
// // fn test<I, O, P: Parser<I, O>>(p: P, s: I) -> PResult<P::Type, ParseError>
// // where
// //     I: VestPublicInput,
// // {
// //     p.parse_fn(s)
// // }
// //
// // fn test2() {
// //     let s = Vec::new();
// //     let r = test::<_, Vec<u8>, _>(parse_pair_of_u8::<&[u8], Vec<u8>>, s.as_slice());
// // }
// // fn parse_pair<I, O, Fst, Snd>(
// //     fst: Fst,
// //     snd: Snd,
// //     s: I,
// // ) -> PResult<(Fst::Type, Snd::Type), ParseError>
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// //     Fst: Parser<I, O>,
// //     Snd: Parser<I, O>,
// // {
// //     // (fst, snd).parse(s)
// // }
// // impl<I, O, C: Combinator<I, O>> Parser<I, O> for C
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// //     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
// // {
// //     type Type = C::Type;
// //
// //     fn parse_fn(&self, s: I) -> PResult<Self::Type, ParseError> {
// //         self.parse(s)
// //     }
// // }
// // impl<I, O, C: Combinator<I, O>> Serializer<I, O> for C
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// //     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
// // {
// //     type Type = C::Type;
// //
// //     fn serialize_fn(
// //         &self,
// //         v: Self::Type,
// //         data: &mut O,
// //         pos: usize,
// //     ) -> SResult<usize, SerializeError> {
// //         self.serialize(v, data, pos)
// //     }
// // }
// // fn parse_pair<I, O, Fst, Snd>(
// //     fst: &Fst,
// //     snd: &Snd,
// //     s: I,
// // ) -> PResult<(Fst::Type, Snd::Type), ParseError>
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// //     Fst: Parser<I, Type = Fst::Type>,
// //     Snd: Parser<I, Type = Snd::Type>,
// // {
// //     let (n, v1) = fst.parse(s.clone())?;
// //     let s_ = s.subrange(n, s.len());
// //     let (m, v2) = snd.parse(s_)?;
// //     if let Some(nm) = n.checked_add(m) {
// //         Ok((nm, (v1, v2)))
// //     } else {
// //         Err(ParseError::SizeOverflow)
// //     }
// // }
// ///////// "Lazy" combinators (`dyn` not supported by Verus yet) to support recursive formats
// // impl<C: View> View for dyn crate::regular::depend::Continuation<(), Output = C> {
// //     type V = C::V;
// //
// //     // spec fn view(&self) -> Self::V;
// // }
// // impl<I, O, C: Combinator<I, O>> Combinator<I, O>
// //     for Box<dyn crate::regular::depend::Continuation<(), Output = C>>
// // where
// //     I: VestInput,
// //     O: VestOutput<I>,
// //     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
// // {
// //     type Type = Box<C::Type>;
// //
// //     fn length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
// //         match self.apply(()).parse(s) {
// //             Ok((n, v)) => Ok((n, Box::new(v))),
// //             Err(e) => Err(e),
// //         }
// //     }
// //
// //     fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
// //         self.apply(()).serialize(*v, data, pos)
// //     }
// // }
// //////// The following works, but currently we cannot verify it due to Verus limitations
// // pub const INSTR_BASE: u8 = 0;
// // pub const AUXBLOCK_BEGIN: u8 = 1;
// // pub const AUXBLOCK_END: u8 = 11;
// //
// // #[derive(Debug)]
// // struct InstrFmt(Either<u8, Box<AuxBlockFmt>>);
// // #[derive(Debug)]
// // struct AuxBlockFmt((u8, (RepeatResult<Box<InstrFmt>>, u8)));
// //
// // impl vstd::view::View for InstrFmt {
// //     type V = Self;
// // }
// // impl vstd::view::View for AuxBlockFmt {
// //     type V = Self;
// // }
// //
// // struct InstrCom(
// //     pub OrdChoice<Refined<U8, TagPred<u8>>, Box<dyn Continuation<(), Output = AuxBlockCom>>>,
// // );
// // struct AuxBlockCom(
// //     pub  (
// //         Refined<U8, TagPred<u8>>,
// //         (
// //             Star<Box<dyn Continuation<(), Output = InstrCom>>>,
// //             Refined<U8, TagPred<u8>>,
// //         ),
// //     ),
// // );
// // impl vstd::view::View for InstrCom {
// //     type V = Self;
// // }
// // impl vstd::view::View for AuxBlockCom {
// //     type V = Self;
// // }
// // impl SpecCombinator for InstrCom {
// //     type Type = InstrFmt;
// // }
// // impl SecureSpecCombinator for InstrCom {}
// // impl SpecCombinator for AuxBlockCom {
// //     type Type = AuxBlockFmt;
// // }
// // impl SecureSpecCombinator for AuxBlockCom {}
// //
// // impl DisjointFrom<Refined<U8, TagPred<u8>>> for AuxBlockCom {}
// //
// // impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrCom {
// //     type Type = InstrFmt;
// //     fn length(&self) -> Option<usize> {
// //         <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
// //     }
// //     fn parse(&self, s: &'a [u8]) -> Result<(usize, Self::Type), ParseError> {
// //         match <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s) {
// //             Ok((n, Either::Left(v))) => Ok((n, InstrFmt(Either::Left(v)))),
// //             Ok((n, Either::Right(v))) => Ok((n, InstrFmt(Either::Right(v)))),
// //             Err(e) => Err(e),
// //         }
// //     }
// //     fn serialize(
// //         &self,
// //         v: Self::Type,
// //         data: &mut Vec<u8>,
// //         pos: usize,
// //     ) -> Result<usize, SerializeError> {
// //         <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v.0, data, pos)
// //     }
// // }
// //
// // impl<'a> Combinator<&'a [u8], Vec<u8>> for AuxBlockCom {
// //     type Type = AuxBlockFmt;
// //     fn length(&self) -> Option<usize> {
// //         <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
// //     }
// //     fn parse(&self, s: &'a [u8]) -> Result<(usize, Self::Type), ParseError> {
// //         match <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s) {
// //             Ok((n, (a, (b, c)))) => Ok((n, AuxBlockFmt((a, (b, c))))),
// //             Err(e) => Err(e),
// //         }
// //     }
// //     fn serialize(
// //         &self,
// //         v: Self::Type,
// //         data: &mut Vec<u8>,
// //         pos: usize,
// //     ) -> Result<usize, SerializeError> {
// //         <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v.0, data, pos)
// //     }
// // }
// //
// // struct AuxBlockCont;
// // struct InstrCont;
// //
// // impl Continuation<()> for AuxBlockCont {
// //     type Output = AuxBlockCom;
// //
// //     fn apply(&self, i: ()) -> Self::Output {
// //         AuxBlockCom((
// //             Refined {
// //                 inner: U8,
// //                 predicate: TagPred(AUXBLOCK_BEGIN),
// //             },
// //             (
// //                 Star(Box::new(InstrCont)),
// //                 Refined {
// //                     inner: U8,
// //                     predicate: TagPred(AUXBLOCK_END),
// //                 },
// //             ),
// //         ))
// //     }
// // }
// //
// // impl Continuation<()> for InstrCont {
// //     type Output = InstrCom;
// //
// //     fn apply(&self, i: ()) -> Self::Output {
// //         InstrCom(OrdChoice(
// //             Refined {
// //                 inner: U8,
// //                 predicate: TagPred(INSTR_BASE),
// //             },
// //             Box::new(AuxBlockCont),
// //         ))
// //     }
// // }
// //
// // fn test() {
// //     // let buf = vec![0x00];
// //     let buf = vec![0x01, 0, 0, 0x01, 0, 0, 0, 0x0B, 0, 0x0B];
// //     let aux_block = AuxBlockCont.apply(());
// //     let instr = InstrCont.apply(());
// //     let (consumed, parsed) = instr.parse(&buf).unwrap_or_else(|e| {
// //         panic!("Failed to parse: {}", e);
// //     });
// //     println!("consumed: {}", consumed);
// //     println!("parsed: {:?}", parsed);
// // }
//
// // Monomorphized approach to lazy combinators
// // Would work if Verus fix https://github.com/verus-lang/verus/issues/1487
// // use crate::regular::choice::Either;
// // use crate::regular::choice::OrdChoice;
// // use crate::regular::depend::Continuation;
// // use crate::regular::disjoint::DisjointFrom;
// // use crate::regular::refined::Refined;
// // use crate::regular::repeat::RepeatResult;
// // use crate::regular::star::Star;
// // use crate::regular::tag::TagPred;
// // use crate::regular::uints::U8;
// // use crate::regular::map::Iso;
// // use crate::regular::map::Mapped;
// // use crate::regular::map::SpecIso;
// //
// // verus! {
// //
// // trait LazyCombinator {
// //     type Comb: View;
// //
// //     spec fn spec_thunk(&self) -> Option<<Self::Comb as View>::V>;
// //
// //     fn thunk(&self) -> (o: Option<Self::Comb>) ensures o matches Some(c) ==> c@ == self.spec_thunk().unwrap();
// // }
// //
// // struct LazyInstrCom(usize);
// // struct LazyAuxBlockCom(usize);
// //
// // impl View for LazyInstrCom {
// //     type V = Self;
// //
// //     open spec fn view(&self) -> Self::V {
// //         *self
// //     }
// // }
// //
// // impl View for LazyAuxBlockCom {
// //     type V = Self;
// //
// //     open spec fn view(&self) -> Self::V {
// //         *self
// //     }
// // }
// //
// // impl LazyCombinator for LazyInstrCom {
// //     type Comb = InstrCom;
// //
// //     closed spec fn spec_thunk(&self) -> Option<<InstrCom as View>::V> {
// //         match self.0 {
// //             0usize => None,
// //             _ => Some(
// //                 SpecInstrCom(
// //                     Mapped {
// //                         inner: OrdChoice(
// //                             Refined { inner: U8, predicate: TagPred(INSTR_BASE) },
// //                             LazyAuxBlockCom((self.0 - 1) as usize),
// //                         ),
// //                         mapper: InstrIso,
// //                     },
// //                 )
// //             )
// //         }
// //     }
// //
// //     fn thunk(&self) -> Option<InstrCom> {
// //         match self.0 {
// //             0 => None,
// //             _ => Some(
// //                 InstrCom(
// //                     Mapped {
// //                         inner: OrdChoice(
// //                             Refined { inner: U8, predicate: TagPred(INSTR_BASE) },
// //                             LazyAuxBlockCom(self.0 - 1),
// //                         ),
// //                         mapper: InstrIso,
// //                     },
// //                 )
// //             )
// //         }
// //     }
// // }
// //
// // impl LazyCombinator for LazyAuxBlockCom {
// //     type Comb = AuxBlockCom;
// //
// //     closed spec fn spec_thunk(&self) -> Option<<AuxBlockCom as View>::V> {
// //         match self.0 {
// //             0usize => None,
// //             _ => Some(
// //                 SpecAuxBlockCom(
// //                     Mapped {
// //                         inner: (
// //                             Refined { inner: U8, predicate: TagPred(AUXBLOCK_BEGIN) },
// //                             (
// //                                 Star(LazyInstrCom((self.0 - 1) as usize)),
// //                                 Refined { inner: U8, predicate: TagPred(AUXBLOCK_END) },
// //                             ),
// //                         ),
// //                         mapper: AuxBlockIso,
// //                     },
// //                 )
// //             )
// //         }
// //     }
// //
// //     fn thunk(&self) -> Option<AuxBlockCom> {
// //         match self.0 {
// //             0 => None,
// //             _ => Some(
// //                 AuxBlockCom(
// //                     Mapped {
// //                         inner: (
// //                             Refined { inner: U8, predicate: TagPred(AUXBLOCK_BEGIN) },
// //                             (
// //                                 Star(LazyInstrCom(self.0 - 1)),
// //                                 Refined { inner: U8, predicate: TagPred(AUXBLOCK_END) },
// //                             ),
// //                         ),
// //                         mapper: AuxBlockIso,
// //                     },
// //                 )
// //             )
// //         }
// //     }
// // }
// //
// // impl SpecCombinator for LazyInstrCom {
// //     type Type = SpecInstrFmt;
// //
// //     closed spec fn spec_parse(&self, s: Seq<u8>) -> PResult<Self::Type, ()> {
// //         match self.spec_thunk() {
// //             Some(c) => c.spec_parse(s),
// //             None => Err(()),
// //         }
// //         // Self::spec_thunk().spec_parse(s)
// //     }
// //
// //     closed spec fn spec_serialize(&self, v: Self::Type) -> SResult<Seq<u8>, ()> {
// //         match self.spec_thunk() {
// //             Some(c) => c.spec_serialize(v),
// //             None => Err(()),
// //         }
// //         // Self::spec_thunk().spec_serialize(v)
// //     }
// // }
// //
// // impl SecureSpecCombinator for LazyInstrCom {
// //     closed spec fn is_prefix_secure() -> bool {
// //         <<Self as LazyCombinator>::Comb as View>::V::is_prefix_secure()
// //     }
// //
// //     closed spec fn is_productive(&self) -> bool {
// //         match self.spec_thunk() {
// //             Some(c) => c.is_productive(),
// //             None => false,
// //         }
// //     }
// //
// //     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
// //         match self.spec_thunk() {
// //             Some(c) => c.theorem_serialize_parse_roundtrip(v),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.theorem_parse_serialize_roundtrip(buf),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.lemma_prefix_secure(s1, s2),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn lemma_parse_length(&self, s: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.lemma_parse_length(s),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn lemma_parse_productive(&self, s: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.lemma_parse_productive(s),
// //             None => {}
// //         }
// //     }
// // }
// //
// // impl SpecCombinator for LazyAuxBlockCom {
// //     type Type = SpecAuxBlockFmt;
// //
// //     closed spec fn spec_parse(&self, s: Seq<u8>) -> PResult<Self::Type, ()> {
// //         match self.spec_thunk() {
// //             Some(c) => c.spec_parse(s),
// //             None => Err(()),
// //         }
// //     }
// //
// //     closed spec fn spec_serialize(&self, v: Self::Type) -> SResult<Seq<u8>, ()> {
// //         match self.spec_thunk() {
// //             Some(c) => c.spec_serialize(v),
// //             None => Err(()),
// //         }
// //     }
// // }
// //
// // impl SecureSpecCombinator for LazyAuxBlockCom {
// //     closed spec fn is_prefix_secure() -> bool {
// //         <<Self as LazyCombinator>::Comb as View>::V::is_prefix_secure()
// //     }
// //
// //     closed spec fn is_productive(&self) -> bool {
// //         match self.spec_thunk() {
// //             Some(c) => c.is_productive(),
// //             None => false,
// //         }
// //     }
// //
// //     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
// //         match self.spec_thunk() {
// //             Some(c) => c.theorem_serialize_parse_roundtrip(v),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.theorem_parse_serialize_roundtrip(buf),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.lemma_prefix_secure(s1, s2),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn lemma_parse_length(&self, s: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.lemma_parse_length(s),
// //             None => {}
// //         }
// //     }
// //
// //     proof fn lemma_parse_productive(&self, s: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.lemma_parse_productive(s),
// //             None => {}
// //         }
// //     }
// // }
// //
// // impl DisjointFrom<Refined<U8, TagPred<u8>>> for LazyAuxBlockCom {
// //     closed spec fn disjoint_from(&self, other: &Refined<U8, TagPred<u8>>) -> bool {
// //         match self.spec_thunk() {
// //             Some(c) => c.0.inner.0.disjoint_from(other),
// //             None => false,
// //         }
// //         // Self::spec_thunk().0.inner.0.disjoint_from(other)
// //         // (self.0)().0.inner.0.disjoint_from(other)
// //     }
// //
// //     proof fn parse_disjoint_on(&self, other: &Refined<U8, TagPred<u8>>, buf: Seq<u8>) {
// //         match self.spec_thunk() {
// //             Some(c) => c.0.inner.0.parse_disjoint_on(other, buf),
// //             None => {}
// //         }
// //         // Self::spec_thunk().0.inner.0.parse_disjoint_on(other, buf)
// //         // (self.0)().0.inner.0.parse_disjoint_on(other, buf)
// //     }
// // }
// //
// // impl<'a> Combinator<&'a [u8], Vec<u8>> for LazyInstrCom
// // {
// //     type Type = Box<InstrFmt>;
// //
// //     closed spec fn spec_length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     closed spec fn parse_requires(&self) -> bool {
// //         forall |c: <Self as LazyCombinator>::Comb| c.parse_requires()
// //     }
// //
// //     fn parse(&self, s: &[u8]) -> PResult<Self::Type, ParseError> {
// //         match self.thunk() {
// //             Some(c) => match c.parse(s) {
// //                 Ok((n, v)) => Ok((n, Box::new(v))),
// //                 Err(e) => Err(e),
// //             },
// //             None => Err(ParseError::Other("Ran out of fuels".to_string())),
// //         }
// //     }
// //
// //     closed spec fn serialize_requires(&self) -> bool {
// //         forall |c: <Self as LazyCombinator>::Comb| c.serialize_requires()
// //     }
// //
// //     fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> SResult<usize, SerializeError> {
// //         match self.thunk() {
// //             Some(c) => c.serialize(*v, data, pos),
// //             None => Err(SerializeError::Other("Ran out of fuels".to_string())),
// //         }
// //     }
// // }
// //
// // impl<'a> Combinator<&'a [u8], Vec<u8>> for LazyAuxBlockCom
// // {
// //     type Type = Box<AuxBlockFmt>;
// //
// //     closed spec fn spec_length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     closed spec fn parse_requires(&self) -> bool {
// //         forall |c: <Self as LazyCombinator>::Comb| c.parse_requires()
// //     }
// //
// //     fn parse(&self, s: &[u8]) -> PResult<Self::Type, ParseError> {
// //         match self.thunk() {
// //             Some(c) => match c.parse(s) {
// //                 Ok((n, v)) => Ok((n, Box::new(v))),
// //                 Err(e) => Err(e),
// //             },
// //             None => Err(ParseError::Other("Ran out of fuels".to_string())),
// //         }
// //     }
// //
// //     closed spec fn serialize_requires(&self) -> bool {
// //         forall |c: <Self as LazyCombinator>::Comb| c.serialize_requires()
// //     }
// //
// //     fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> SResult<usize, SerializeError> {
// //         match self.thunk() {
// //             Some(c) => c.serialize(*v, data, pos),
// //             None => Err(SerializeError::Other("Ran out of fuels".to_string())),
// //         }
// //     }
// // }
// //
// //
// // // impl<T: SpecCombinator> SpecCombinator for spec_fn() -> T {
// // //     type Type = T::Type;
// // //
// // //     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
// // //         self().spec_parse(s)
// // //     }
// // //
// // //     open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
// // //         self().spec_serialize(v)
// // //     }
// // // }
// // //
// // // impl<T: SecureSpecCombinator> SecureSpecCombinator for spec_fn() -> T {
// // //     open spec fn is_prefix_secure() -> bool {
// // //         T::is_prefix_secure()
// // //     }
// // //
// // //     open spec fn is_productive(&self) -> bool {
// // //         self().is_productive()
// // //     }
// // //
// // //     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
// // //         self().theorem_serialize_parse_roundtrip(v)
// // //     }
// // //
// // //     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
// // //         self().theorem_parse_serialize_roundtrip(buf)
// // //     }
// // //
// // //     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
// // //         self().lemma_prefix_secure(s1, s2)
// // //     }
// // //
// // //     proof fn lemma_parse_length(&self, s: Seq<u8>) {
// // //         self().lemma_parse_length(s)
// // //     }
// // //
// // //     proof fn lemma_parse_productive(&self, s: Seq<u8>) {
// // //         self().lemma_parse_productive(s)
// // //     }
// // // }
// //
// //
// // pub const INSTR_BASE: u8 = 0;
// //
// // pub const AUXBLOCK_BEGIN: u8 = 1;
// //
// // pub const AUXBLOCK_END: u8 = 11;
// //
// // ghost enum SpecInstrFmt {
// //     Base(u8),
// //     Block(SpecAuxBlockFmt),
// // }
// //
// // type SpecInstrFmtAlias = Either<u8, SpecAuxBlockFmt>;
// //
// // ghost struct SpecAuxBlockFmt {
// //     begin: u8,
// //     instrs: Seq<SpecInstrFmt>,
// //     end: u8,
// // }
// //
// // type SpecAuxBlockFmtAlias = (u8, (Seq<SpecInstrFmt>, u8));
// //
// // #[derive(Debug)]
// // enum InstrFmt {
// //     Base(u8),
// //     Block(Box<AuxBlockFmt>),
// // }
// //
// // type InstrFmtAlias = Either<u8, Box<AuxBlockFmt>>;
// //
// // #[derive(Debug)]
// // struct AuxBlockFmt {
// //     begin: u8,
// //     instrs: RepeatResult<Box<InstrFmt>>,
// //     end: u8,
// // }
// //
// // type AuxBlockFmtAlias = (u8, (RepeatResult<Box<InstrFmt>>, u8));
// //
// // impl View for InstrFmt {
// //     type V = SpecInstrFmt;
// //
// //     closed spec fn view(&self) -> Self::V {
// //         match self {
// //             InstrFmt::Base(v) => SpecInstrFmt::Base(*v),
// //             InstrFmt::Block(v) => SpecInstrFmt::Block(v@),
// //         }
// //     }
// // }
// //
// // impl View for AuxBlockFmt {
// //     type V = SpecAuxBlockFmt;
// //
// //     closed spec fn view(&self) -> Self::V {
// //         SpecAuxBlockFmt { begin: self.begin, instrs: self.instrs.view(), end: self.end }
// //     }
// // }
// //
// // impl SpecFrom<SpecInstrFmtAlias> for SpecInstrFmt {
// //     closed spec fn spec_from(v: SpecInstrFmtAlias) -> Self {
// //         match v {
// //             Either::Left(v) => SpecInstrFmt::Base(v),
// //             Either::Right(v) => SpecInstrFmt::Block(v),
// //         }
// //     }
// // }
// //
// // impl SpecFrom<SpecInstrFmt> for SpecInstrFmtAlias {
// //     closed spec fn spec_from(v: SpecInstrFmt) -> Self {
// //         match v {
// //             SpecInstrFmt::Base(v) => Either::Left(v),
// //             SpecInstrFmt::Block(v) => Either::Right(v),
// //         }
// //     }
// // }
// //
// // impl SpecFrom<SpecAuxBlockFmtAlias> for SpecAuxBlockFmt {
// //     closed spec fn spec_from(v: SpecAuxBlockFmtAlias) -> Self {
// //         let (begin, (instrs, end)) = v;
// //         SpecAuxBlockFmt { begin, instrs, end }
// //     }
// // }
// //
// // impl SpecFrom<SpecAuxBlockFmt> for SpecAuxBlockFmtAlias {
// //     closed spec fn spec_from(v: SpecAuxBlockFmt) -> Self {
// //         (v.begin, (v.instrs, v.end))
// //     }
// // }
// //
// // impl From<InstrFmtAlias> for InstrFmt {
// //     fn ex_from(v: InstrFmtAlias) -> Self {
// //         match v {
// //             Either::Left(v) => InstrFmt::Base(v),
// //             Either::Right(v) => InstrFmt::Block(v),
// //         }
// //     }
// // }
// //
// // impl From<InstrFmt> for InstrFmtAlias {
// //     fn ex_from(v: InstrFmt) -> Self {
// //         match v {
// //             InstrFmt::Base(v) => Either::Left(v),
// //             InstrFmt::Block(v) => Either::Right(v),
// //         }
// //     }
// // }
// //
// // impl From<AuxBlockFmtAlias> for AuxBlockFmt {
// //     fn ex_from(v: AuxBlockFmtAlias) -> Self {
// //         let (begin, (instrs, end)) = v;
// //         AuxBlockFmt { begin, instrs, end }
// //     }
// // }
// //
// // impl From<AuxBlockFmt> for AuxBlockFmtAlias {
// //     fn ex_from(v: AuxBlockFmt) -> Self {
// //         (v.begin, (v.instrs, v.end))
// //     }
// // }
// //
// // struct InstrIso;
// //
// // impl View for InstrIso {
// //     type V = Self;
// //
// //     closed spec fn view(&self) -> Self::V {
// //         InstrIso
// //     }
// // }
// //
// // impl SpecIso for InstrIso {
// //     type Src = SpecInstrFmtAlias;
// //
// //     type Dst = SpecInstrFmt;
// //
// //     proof fn spec_iso(s: Self::Src) {
// //     }
// //
// //     proof fn spec_iso_rev(s: Self::Dst) {
// //     }
// // }
// //
// // impl Iso for InstrIso {
// //     type Src = InstrFmtAlias;
// //
// //     type Dst = InstrFmt;
// // }
// //
// // struct AuxBlockIso;
// //
// // impl View for AuxBlockIso {
// //     type V = Self;
// //
// //     closed spec fn view(&self) -> Self::V {
// //         AuxBlockIso
// //     }
// // }
// //
// // impl SpecIso for AuxBlockIso {
// //     type Src = SpecAuxBlockFmtAlias;
// //
// //     type Dst = SpecAuxBlockFmt;
// //
// //     proof fn spec_iso(s: Self::Src) {
// //     }
// //
// //     proof fn spec_iso_rev(s: Self::Dst) {
// //     }
// // }
// //
// // impl Iso for AuxBlockIso {
// //     type Src = AuxBlockFmtAlias;
// //
// //     type Dst = AuxBlockFmt;
// // }
// //
// // struct InstrCom(pub Mapped<OrdChoice<Refined<U8, TagPred<u8>>, LazyAuxBlockCom>, InstrIso>);
// //
// // struct AuxBlockCom(
// //     pub Mapped<
// //         (Refined<U8, TagPred<u8>>, (Star<LazyInstrCom>, Refined<U8, TagPred<u8>>)),
// //         AuxBlockIso,
// //     >,
// // );
// //
// // struct SpecInstrCom(pub SpecInstrComInner);
// //
// // struct SpecAuxBlockCom(pub SpecAuxBlockComInner);
// //
// // type SpecInstrComInner = Mapped<
// //     OrdChoice<Refined<U8, TagPred<u8>>, LazyAuxBlockCom>,
// //     InstrIso,
// // >;
// //
// // type SpecAuxBlockComInner = Mapped<
// //     (Refined<U8, TagPred<u8>>, (Star<LazyInstrCom>, Refined<U8, TagPred<u8>>)),
// //     AuxBlockIso,
// // >;
// //
// // impl View for InstrCom {
// //     type V = SpecInstrCom;
// //
// //     closed spec fn view(&self) -> Self::V {
// //         SpecInstrCom(self.0@)
// //     }
// // }
// //
// // impl View for AuxBlockCom {
// //     type V = SpecAuxBlockCom;
// //
// //     closed spec fn view(&self) -> Self::V {
// //         SpecAuxBlockCom(self.0@)
// //     }
// // }
// //
// // impl SpecCombinator for SpecInstrCom {
// //     type Type = SpecInstrFmt;
// //
// //     closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
// //         self.0.spec_parse(s)
// //     }
// //
// //     closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
// //         self.0.spec_serialize(v)
// //     }
// // }
// //
// // impl SecureSpecCombinator for SpecInstrCom {
// //     open spec fn is_prefix_secure() -> bool {
// //         SpecInstrComInner::is_prefix_secure()
// //     }
// //
// //     open spec fn is_productive(&self) -> bool {
// //         self.0.is_productive()
// //     }
// //
// //     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
// //         // self.0.theorem_serialize_parse_roundtrip(v.0)
// //         self.0.theorem_serialize_parse_roundtrip(v)
// //     }
// //
// //     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
// //         self.0.theorem_parse_serialize_roundtrip(buf)
// //     }
// //
// //     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
// //         self.0.lemma_prefix_secure(s1, s2)
// //     }
// //
// //     proof fn lemma_parse_length(&self, s: Seq<u8>) {
// //         self.0.lemma_parse_length(s)
// //     }
// //
// //     proof fn lemma_parse_productive(&self, s: Seq<u8>) {
// //         self.0.lemma_parse_productive(s)
// //     }
// // }
// //
// // impl SpecCombinator for SpecAuxBlockCom {
// //     type Type = SpecAuxBlockFmt;
// //
// //     closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
// //         self.0.spec_parse(s)
// //     }
// //
// //     closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
// //         self.0.spec_serialize(v)
// //     }
// // }
// //
// // impl SecureSpecCombinator for SpecAuxBlockCom {
// //     open spec fn is_prefix_secure() -> bool {
// //         SpecAuxBlockComInner::is_prefix_secure()
// //     }
// //
// //     open spec fn is_productive(&self) -> bool {
// //         self.0.is_productive()
// //     }
// //
// //     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
// //         self.0.theorem_serialize_parse_roundtrip(v)
// //
// //     }
// //
// //     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
// //         self.0.theorem_parse_serialize_roundtrip(buf)
// //     }
// //
// //     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
// //         self.0.lemma_prefix_secure(s1, s2)
// //     }
// //
// //     proof fn lemma_parse_length(&self, s: Seq<u8>) {
// //         self.0.lemma_parse_length(s)
// //     }
// //
// //     proof fn lemma_parse_productive(&self, s: Seq<u8>) {
// //         self.0.lemma_parse_productive(s)
// //     }
// // }
// //
// // // impl DisjointFrom<Refined<U8, TagPred<u8>>> for SpecAuxBlockCont {
// // //     closed spec fn disjoint_from(&self, other: &Refined<U8, TagPred<u8>>) -> bool {
// // //         (self.0)().0.inner.0.disjoint_from(other)
// // //     }
// // //
// // //     proof fn parse_disjoint_on(&self, other: &Refined<U8, TagPred<u8>>, buf: Seq<u8>) {
// // //         (self.0)().0.inner.0.parse_disjoint_on(other, buf)
// // //     }
// // // }
// //
// // // impl DisjointFrom<Refined<U8, TagPred<u8>>> for SpecInstrCom {}
// // impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrCom {
// //     type Type = InstrFmt;
// //
// //     open spec fn spec_length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn parse(&self, s: &'a [u8]) -> Result<(usize, Self::Type), ParseError> {
// //         <_ as Combinator<&[u8], Vec<u8>>>::parse(
// //             &self.0,
// //             s,
// //         )
// //     }
// //
// //     fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> Result<
// //         usize,
// //         SerializeError,
// //     > {
// //         <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
// //     }
// // }
// //
// // impl<'a> Combinator<&'a [u8], Vec<u8>> for AuxBlockCom {
// //     type Type = AuxBlockFmt;
// //
// //     open spec fn spec_length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn length(&self) -> Option<usize> {
// //         None
// //     }
// //
// //     fn parse(&self, s: &'a [u8]) -> Result<(usize, Self::Type), ParseError> {
// //         <_ as Combinator<&[u8], Vec<u8>>>::parse(
// //             &self.0,
// //             s,
// //         )
// //     }
// //
// //     fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> Result<
// //         usize,
// //         SerializeError,
// //     > {
// //         <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
// //     }
// // }
// //
// // } // verus!
