pub use crate::errors::*;
pub use crate::utils::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::*;
use std::rc::Rc;

verus! {

/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type SpecResult;

    /// The specification of [`Combinator::parse`].
    spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>;

    /// The specification of [`Combinator::serialize`].
    spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>;

    /// A helper fact to ensure that the result of parsing is within the input bounds.
    proof fn spec_parse_wf(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s) matches Ok((n, _)) ==> n <= s.len(),
    ;
}

/// Theorems and lemmas that must be proven for a combinator to be considered correct and secure.
pub trait SecureSpecCombinator: SpecCombinator {
    /// Like an associated constant, denotes whether the combinator is prefix-secure.
    spec fn is_prefix_secure() -> bool;

    /// One of the top-level roundtrip properties
    /// It reads "if we successfully serialize a value, then parsing the serialized bytes should
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
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
        ensures
            self.spec_serialize(v) matches Ok(b) ==> self.spec_parse(b) == Ok::<_, ()>(
                (b.len() as usize, v),
            ),
    ;

    /// Followed from `theorem_serialize_parse_roundtrip`
    proof fn corollary_parse_surjective(&self, v: Self::SpecResult)
        requires
            self.spec_serialize(v) is Ok,
        ensures
            exists |b: Seq<u8>| {
                &&& self.spec_parse(b) is Ok
                &&& self.spec_parse(b) matches Ok((n, v_)) && v_ == v
            }
    {
        self.theorem_serialize_parse_roundtrip(v);
    }

    /// Followed from `theorem_serialize_parse_roundtrip`
    proof fn corollary_serialize_injective(&self, v1: Self::SpecResult, v2: Self::SpecResult)
        ensures
            self.spec_serialize(v1) matches Ok(b1) ==> self.spec_serialize(v2) matches Ok(b2) ==> b1
                == b2 ==> v1 == v2,
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
    ///   byte sequence.
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        requires
            buf.len() <= usize::MAX,
        ensures
            self.spec_parse(buf) matches Ok((n, v)) ==> self.spec_serialize(v) == Ok::<_, ()>(
                buf.subrange(0, n as int),
            ),
    ;

    /// Followed from `theorem_parse_serialize_roundtrip`
    proof fn corollary_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            buf1.len() <= usize::MAX,
            buf2.len() <= usize::MAX,
        ensures
            self.spec_parse(buf1) matches Ok((n1, v1)) ==> self.spec_parse(buf2) matches Ok(
                (n2, v2),
            ) ==> v1 == v2 ==> buf1.subrange(0, n1 as int) == buf2.subrange(0, n2 as int),
    {
        self.theorem_parse_serialize_roundtrip(buf1);
        self.theorem_parse_serialize_roundtrip(buf2);
    }

    /// This prefix-secure lemma is used in the proof of the roundtrip properties for sequencing
    /// combinators.
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        requires
            s1.len() + s2.len() <= usize::MAX,
        ensures
            Self::is_prefix_secure() ==> self.spec_parse(s1).is_ok() ==> self.spec_parse(s1.add(s2))
                == self.spec_parse(s1),
    ;
}

/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte buffers. 
/// `VestSecretInput` does not expose the contents of the buffer, so opaque buffer types for side-channel
/// security can implement `VestSecretInput`.
pub trait VestSecretInput: View<V = Seq<u8>> {
    /// The length of the buffer.    
    fn len(&self) -> (res: usize)
        ensures
            res == self@.len(),
    ;

    /// Analogous to `vstd::slice_subrange`
    fn subrange(&self, i: usize, j: usize) -> (res: Self)
    where Self: Sized
        requires
            0 <= i <= j <= self@.len(),
        ensures
            res@ == self@.subrange(i as int, j as int),
    ;

    /// Creates another buffer with the same contents.
    /// For good performance, this function should be cheap, just creating a new reference rather than
    /// actually copying the buffer.
    fn clone(&self) -> (res: Self)
    where Self: Sized
        ensures
            res@ == self@
    ;
}

/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte buffers. 
pub trait VestInput: VestSecretInput {
    /// Returns a byte slice with the contents of the buffer
    fn as_byte_slice(&self) -> (res: &[u8])
        ensures
            res@ == self@,
    ;
}

impl<'a> VestSecretInput for &'a [u8] {
    fn len(&self) -> usize {
        <[u8]>::len(self)
    }

    fn subrange(&self, i: usize, j: usize) -> &'a [u8] {
        slice_subrange(*self, i, j)
    }

    fn clone(&self) -> &'a [u8] {
        *self
    }
}

impl<'a> VestInput for &'a [u8] {
    fn as_byte_slice(&self) -> &[u8] {
        *self
    }
}

/// Provided to demonstrate flexibility of the trait, but likely should not be used,
/// since this impl copies the `Vec` every time you call `subrange` or `clone`.
impl VestSecretInput for Vec<u8> {
    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn subrange(&self, i: usize, j: usize) -> Vec<u8> {
        let mut res = Vec::new();
        vec_u8_extend_from_slice(&mut res, slice_subrange(self.as_slice(), i, j));
        proof { assert_seqs_equal!(res@, self@.subrange(i as int, j as int)); }
        res
    }

    fn clone(&self) -> Vec<u8> {
        Clone::clone(self)
    }
}

impl VestInput for Vec<u8> {
    fn as_byte_slice(&self) -> &[u8] {
        self.as_slice()
    }
}

/// Provided to demonstrate flexibility of the trait, but likely should not be used,
/// since this impl copies the `Vec` every time you call `subrange` or `clone`.
impl VestSecretInput for Rc<Vec<u8>> {
    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn subrange(&self, i: usize, j: usize) -> Rc<Vec<u8>> {
        let mut res = Vec::new();
        vec_u8_extend_from_slice(&mut res, slice_subrange(self.as_slice(), i, j));
        proof { assert_seqs_equal!(res@, self@.subrange(i as int, j as int)); }
        Rc::new(res)
    }

    fn clone(&self) -> Rc<Vec<u8>> {
        Clone::clone(self)
    }
}

impl VestInput for Rc<Vec<u8>> {
    fn as_byte_slice(&self) -> &[u8] {
        self.as_slice()
    }
}

/// Trait for types that can be used as output for Vest serializers.
/// `VestSecretOutput` does not expose the contents of the buffer, so opaque buffer types for side-channel
/// security can implement `VestSecretOutput`.
pub trait VestSecretOutput<I>: View<V = Seq<u8>> where 
    I: View<V = Seq<u8>>
{
    /// The length of the buffer.    
    fn len(&self) -> (res: usize)
        ensures
            res == self@.len(),
    ;

    /// Copy `input` to `self` starting at index `i`.
    fn set_range(&mut self, i: usize, input: I) -> (res: ()) 
        requires
            0 <= i + input@.len() <= old(self)@.len() <= usize::MAX,
        ensures 
            self@.len() == old(self)@.len() 
            && self@ == old(self)@.subrange(0, i as int)
                            .add(input@)
                            .add(old(self)@.subrange(i + input@.len(), self@.len() as int))
    ;
}

impl<I> VestSecretOutput<I> for Vec<u8> where
    I: VestInput
{
    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn set_range(&mut self, i: usize, input: I) {
        set_range(self, i, input.as_byte_slice());
    }
}

/// Trait for types that can be used as output for Vest serializers.
/// `VestOutput` can be set using transparent bytes, so it cannot provide type abstraction for side-channel security.
pub trait VestOutput<I>: VestSecretOutput<I> where 
    I: View<V = Seq<u8>>
{
    /// Set the byte at index `i` to `value`.
    fn set_byte(&mut self, i: usize, value: u8)
        requires
            i < old(self)@.len(),
        ensures
            self@ == old(self)@.update(i as int, value),
    ;

    /// Copy `input` to `self` starting at index `i`. (Same as `set_range` but with byte slice input.)
    fn set_byte_range(&mut self, i: usize, input: &[u8]) -> (res: ()) 
        requires
            0 <= i + input@.len() <= old(self)@.len() <= usize::MAX,
        ensures 
            self@.len() == old(self)@.len() 
            && self@ == old(self)@.subrange(0, i as int)
                            .add(input@)
                            .add(old(self)@.subrange(i + input@.len(), self@.len() as int))
    ;
}

impl<I> VestOutput<I> for Vec<u8> where
    I: VestInput
{
    fn set_byte(&mut self, i: usize, value: u8) {
        self.set(i, value);
    }

    fn set_byte_range(&mut self, i: usize, input: &[u8]) {
        set_range(self, i, input);
    }
}


/// Implementation for parser and serializer combinators. A combinator's view must be a
/// [`SecureSpecCombinator`].
pub trait Combinator<I, O>: View where
    I: VestInput,
    O: VestOutput<I>,
    Self::V: SecureSpecCombinator<SpecResult = <Self::Result as View>::V>,
 {
    /// The result type of parsing and the input type of serialization.
    type Result: View;

    /// Spec version of [`Self::length`].
    spec fn spec_length(&self) -> Option<usize>;

    /// The length of the output buffer, if known.
    /// This can be used to optimize serialization by pre-allocating the buffer.
    fn length(&self) -> (res: Option<usize>)
        ensures
            res == self.spec_length(),
    ;

    /// Pre-condition for parsing.
    open spec fn parse_requires(&self) -> bool {
        true
    }

    /// The parsing function.
    fn parse(&self, s: I) -> (res: Result<(usize, Self::Result), ParseError>)
        requires
            self.parse_requires(),
        ensures
            res matches Ok((n, v)) ==> {
                &&& self@.spec_parse(s@) is Ok
                &&& self@.spec_parse(s@) matches Ok((m, w)) ==> n == m && v@ == w && n <= s@.len()
            },
            res is Err ==> self@.spec_parse(s@) is Err,
            self@.spec_parse(s@) matches Ok((m, w)) ==> {
                &&& res is Ok
                &&& res matches Ok((n, v)) ==> m == n && w == v@
            },
            self@.spec_parse(s@) is Err ==> res is Err,
    ;

    /// Pre-condition for serialization.
    open spec fn serialize_requires(&self) -> bool {
        true
    }

    /// The serialization function.
    fn serialize(&self, v: Self::Result, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >)
        requires
            self.serialize_requires(),
        ensures
            data@.len() == old(data)@.len(),
            res matches Ok(n) ==> {
                &&& self@.spec_serialize(v@) is Ok
                &&& self@.spec_serialize(v@) matches Ok(b) ==> {
                    n == b.len() && data@ == seq_splice(old(data)@, pos, b)
                }
            },
    ;
}

impl<C: SpecCombinator> SpecCombinator for &C {
    type SpecResult = C::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        (*self).spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        (*self).spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        (*self).spec_parse_wf(s)
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for &C {
    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        (*self).theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (*self).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        (*self).lemma_prefix_secure(s1, s2)
    }
}

impl<I, O, C: Combinator<I, O>> Combinator<I, O> for &C where
    I: VestInput,
    O: VestOutput<I>,
    C::V: SecureSpecCombinator<SpecResult = <C::Result as View>::V>,
 {
    type Result = C::Result;

    open spec fn spec_length(&self) -> Option<usize> {
        (*self).spec_length()
    }

    fn length(&self) -> Option<usize> {
        (*self).length()
    }

    open spec fn parse_requires(&self) -> bool {
        (*self).parse_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Result), ParseError>) {
        (*self).parse(s)
    }

    open spec fn serialize_requires(&self) -> bool {
        (*self).serialize_requires()
    }

    fn serialize(&self, v: Self::Result, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        (*self).serialize(v, data, pos)
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
// #[verifier::reject_recursive_types(SpecResult)]
// pub struct SpecCombinatorFn<SpecResult, const Prefix: u8> {
//     pub parse: spec_fn(Seq<u8>) -> Result<(usize, SpecResult), ()>,
//     pub serialize: spec_fn(SpecResult) -> Result<Seq<u8>, ()>,
// }
//
// impl<SpecResult, const Prefix: u8> SpecCombinatorFn<SpecResult, Prefix> {
//     pub open spec fn new(
//         parse: spec_fn(Seq<u8>) -> Result<(usize, SpecResult), ()>,
//         serialize: spec_fn(SpecResult) -> Result<Seq<u8>, ()>,
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
//         parse: spec_fn(Seq<u8>) -> Result<(usize, SpecResult), ()>,
//         serialize: spec_fn(SpecResult) -> Result<Seq<u8>, ()>,
//         v: SpecResult,
//     ) -> bool {
//         serialize(v) is Ok ==> parse(serialize(v).unwrap()) == Ok::<_, ()>(
//             (serialize(v).unwrap().len() as usize, v),
//         )
//     }
//
//     pub open spec fn theorem_parse_serialize_roundtrip(
//         parse: spec_fn(Seq<u8>) -> Result<(usize, SpecResult), ()>,
//         serialize: spec_fn(SpecResult) -> Result<Seq<u8>, ()>,
//         buf: Seq<u8>,
//     ) -> bool {
//         buf.len() <= usize::MAX ==> parse(buf) is Ok ==> serialize(parse(buf).unwrap().1) == Ok::<
//             _,
//             (),
//         >(buf.subrange(0, parse(buf).unwrap().0 as int))
//     }
//
//     pub open spec fn lemma_prefix_secure(
//         parse: spec_fn(Seq<u8>) -> Result<(usize, SpecResult), ()>,
//         s1: Seq<u8>,
//         s2: Seq<u8>,
//     ) -> bool {
//         if s1.len() + s2.len() <= usize::MAX {
//             (Prefix == 1) ==> parse(s1) is Ok ==> parse(s1.add(s2)) == parse(s1)
//         } else {
//             true
//         }
//     }
// }
//
//
// impl<SpecResult, const Prefix: u8> SpecCombinator for SpecCombinatorFn<SpecResult, Prefix> {
//     type SpecResult = SpecResult;
//
//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
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
//     open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
//         (self.serialize)(v)
//     }
//
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//     }
// }
//
// impl<SpecResult, const Prefix: u8> SecureSpecCombinator for SpecCombinatorFn<SpecResult, Prefix> {
//     open spec fn spec_is_prefix_secure() -> bool {
//         Prefix == 1
//     }
//
//     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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
// pub struct CombinatorFn<'a, 'b, R, P, S, const Prefix: u8> where
//     R: View,
//     P: Fn(&'a [u8]) -> Result<(usize, R), ()>,
//     S: Fn(R, &'b mut Vec<u8>, usize) -> Result<usize, ()>,
// {
//     pub parse: P,
//     pub serialize: S,
//     pub spec_parse: Ghost<spec_fn(Seq<u8>) -> Result<(usize, R::V), ()>>,
//     pub spec_serialize: Ghost<spec_fn(R::V) -> Result<Seq<u8>, ()>>,
//     pub _phantom: std::marker::PhantomData<&'b &'a R>,
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
//     Self::V: SecureSpecCombinator<SpecResult = R::V>,
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
