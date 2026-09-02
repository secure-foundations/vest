//! Executable serializer traits.
use crate::core::exec::output::*;
use crate::core::spec::{Consistency, GoodSerializer, SpecByteLen, SpecSerializer};
use core::fmt;
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use vstd::prelude::*;

verus! {

/// An executable serializer targeting `Output`.
pub trait Serializer<Output, T> where
    Output: OutputBuf,
    Self: SpecByteLen<T = T::V> + SpecSerializer<SVal = T::V> + Consistency<Val = T::V>,
    T: DeepView + ?Sized,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        true
    }

    /// Serializes the value `v` into the output buffer `obuf` by (logically) appending the serialized bytes to the end of `obuf`.
    /// This view has two main benefits:
    /// 1. It matches the [specification](SpecSerializer) of the serializer closely, which simplifies the proofs;
    /// 2. It is general enough to support both fixed-size (e.g., `&mut [u8]`) and growable (e.g., `Vec<u8>`) output buffers (see [`OutputBuf`]).
    ///
    /// ## Preconditions
    ///
    /// - The serializer's execution invariant holds (mainly used for [`super::fns::FnSerializer`], usually trivial for most combinators).
    /// - The value `v` is [compliant](Consistency) with the format specification.
    /// - The output buffer has enough space to hold the serialized value.
    ///
    /// ## Postconditions
    ///
    /// - The output buffer's contents are extended by the serialized value.
    /// - The output buffer's remaining capacity is reduced by the serialized value's length.
    /// - The output buffer's destination remains the same.
    fn serialize_into(&self, v: &T, obuf: &mut Output)
        requires
            self.exec_inv(),
            self.consistent(v.deep_view()),
            old(obuf).fits(self.byte_len(v.deep_view())),
        ensures
            final(obuf)@ == old(obuf)@ + self.spec_serialize(v.deep_view()),
            forall|n| old(obuf).fits(self.byte_len(v.deep_view()) + n) <==> final(obuf).fits(n),
            old(obuf).same_destination(final(obuf)),
    ;
}

/// Convenience entry points for the two standard output destinations.
pub trait SerializerExt<T> where
    Self: SpecByteLen<T = T::V> + SpecSerializer<SVal = T::V> + Consistency<Val = T::V>,
    T: DeepView + ?Sized,
 {
    /// Serializes into an exactly-sized caller-provided slice without allocating.
    fn serialize<'a>(&self, v: &T, obuf: &'a mut [u8]) where Self: Serializer<OutputSlice<'a>, T>
        requires
            self.exec_inv(),
            self.consistent(v.deep_view()),
            obuf@.len() == self.byte_len(v.deep_view()),
        ensures
            final(obuf)@ == self.spec_serialize(v.deep_view()),
    {
        let mut output = OutputSlice::new(obuf);
        self.serialize_into(v, &mut output);
        proof {
            assert(output.fits(0));
            assert(!output.fits(1));
            assert(output.pos == output.obuf@.len());
        }
    }

    /// Serializes by appending to a growable Vec (though the Vec can be preallocated with [`Prepare`]/[`ByteLen`]).
    #[cfg(feature = "alloc")]
    fn serialize_with_vec(&self, v: &T, obuf: &mut Vec<u8>) where Self: Serializer<Vec<u8>, T>
        requires
            self.exec_inv(),
            self.consistent(v.deep_view()),
        ensures
            final(obuf)@ == old(obuf)@ + self.spec_serialize(v.deep_view()),
    {
        self.serialize_into(v, obuf);
    }
}

impl<T: DeepView + ?Sized, S> SerializerExt<T> for S where
    S: SpecByteLen<T = T::V> + SpecSerializer<SVal = T::V> + Consistency<Val = T::V>,
 {

}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
/// Why a value does not satisfy a format's specification.
pub enum ComplianceErrorKind {
    /// A stored or derived length does not match the corresponding value.
    LengthInconsistent,
    /// A tag is outside the domain accepted by the format.
    InvalidTag,
    /// A [`Refined`](crate::combinators::Refined) predicate rejected the value.
    PredicateFailed,
    /// A conditional combinator is disabled for this value.
    CondRejected,
    /// A recursive value exceeds the format's configured recursion limit.
    RecursionLimitExceeded,
    /// No branch of a choice accepts the value.
    InvalidChoice,
    /// A format-specific consistency error.
    Custom(&'static str),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
/// Top-level reason that preparation failed.
pub enum PreSerializeErrorKind {
    /// The exact serialized length cannot be represented by `usize`.
    LengthTooLarge,
    /// The value is not accepted by the format.
    NotCompliant(ComplianceErrorKind),
}

#[derive(Debug, PartialEq, Eq)]
/// Error returned by [`Prepare::prepare`].
///
/// `failed_format` identifies the innermost named format that attached
/// context. With the `alloc` feature, `format_stack` retains the complete
/// format trace.
pub struct PreSerializeError {
    /// The underlying failure category.
    pub kind: PreSerializeErrorKind,
    /// The innermost named format that reported the failure, if available.
    pub failed_format: Option<&'static str>,
    #[cfg(feature = "alloc")]
    /// Nested format names collected while propagating the error.
    pub format_stack: Vec<&'static str>,
}

impl Clone for PreSerializeError {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind,
            failed_format: self.failed_format,
            #[cfg(feature = "alloc")]
            format_stack: self.format_stack.clone(),
        }
    }
}

impl PreSerializeError {
    /// Creates an error without attached format context.
    pub fn new(kind: PreSerializeErrorKind) -> Self {
        Self {
            kind,
            failed_format: None,
            #[cfg(feature = "alloc")]
            format_stack: Vec::new(),
        }
    }

    /// Creates a serialized-length overflow error.
    pub fn length_too_large() -> Self {
        Self::new(PreSerializeErrorKind::LengthTooLarge)
    }

    /// Creates a value-compliance error.
    pub fn not_compliant(kind: ComplianceErrorKind) -> Self {
        Self::new(PreSerializeErrorKind::NotCompliant(kind))
    }

    /// Creates a format-specific value-compliance error.
    pub fn custom(msg: &'static str) -> Self {
        Self::new(PreSerializeErrorKind::NotCompliant(ComplianceErrorKind::Custom(msg)))
    }

    /// Adds a named format to the error's propagation trace.
    pub fn push_format(self, current_format: &'static str) -> Self {
        let mut err = self;
        if err.failed_format.is_none() {
            err.failed_format = Some(current_format);
        }
        #[cfg(feature = "alloc")]
        {
            err.format_stack.push(current_format);
        }
        err
    }

    /// Returns the innermost named format that attached context.
    pub fn failed_format(&self) -> Option<&'static str> {
        self.failed_format
    }

    /// Returns the collected format trace, or an empty slice without `alloc`.
    pub fn format_trace(&self) -> &[&'static str] {
        #[cfg(feature = "alloc")]
        { self.format_stack.as_slice() }
        #[cfg(not(feature = "alloc"))]
        { &[] }
    }
}

/// Checks that a value can be serialized and computes its exact output length.
///
/// Call this before allocating an output or invoking [`SerializerExt::serialize`]
/// on a value whose consistency has not already been established.
pub trait Prepare<T>: SpecByteLen<T = T::V> + Consistency<Val = T::V> where T: DeepView + ?Sized {
    /// Extra invariant required by the executable preparation implementation.
    open spec fn exec_inv(&self) -> bool {
        true
    }

    /// Validates `v` and returns its exact serialized length.
    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>)
        requires
            self.exec_inv(),
        ensures
            checked matches Ok(len) ==> {
                &&& self.consistent(v.deep_view())
                &&& len == self.byte_len(v.deep_view())
            },
    ;
}

/// Computes the exact serialized length of a value already known to fit `usize`.
///
/// Unlike [`Prepare`], this operation does not check the format's consistency
/// predicate. Use `Prepare::prepare` for untrusted or newly constructed values.
pub trait ByteLen<T> where Self: SpecByteLen<T = T::V>, T: DeepView + ?Sized {
    /// Extra invariant required by the executable length implementation.
    open spec fn exec_inv(&self) -> bool {
        true
    }

    /// Returns the exact number of bytes produced by serialization.
    fn length(&self, v: &T) -> (len: usize)
        requires
            self.exec_inv(),
            self.byte_len(v.deep_view()) <= usize::MAX,
        ensures
            len == self.byte_len(v.deep_view()),
    ;
}

impl<T: ?Sized, S> Prepare<T> for &S where T: DeepView, S: Prepare<T> {
    open spec fn exec_inv(&self) -> bool {
        (*self).exec_inv()
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        (*self).prepare(v)
    }
}

impl<T: ?Sized, S> ByteLen<T> for &S where T: DeepView, S: ByteLen<T> {
    open spec fn exec_inv(&self) -> bool {
        (*self).exec_inv()
    }

    fn length(&self, v: &T) -> (len: usize) {
        (*self).length(v)
    }
}

impl<S: SpecSerializer> SpecSerializer for &S {
    type SVal = S::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (*self).spec_serialize(v)
    }
}

impl<S: SpecByteLen> SpecByteLen for &S {
    type T = S::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (*self).byte_len(v)
    }
}

impl<S: GoodSerializer> GoodSerializer for &S {
    open spec fn serialize_inv(&self) -> bool {
        (*self).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        (*self).lemma_serialize_len(v)
    }
}

impl<S: Consistency> Consistency for &S {
    type Val = S::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (*self).consistent(v)
    }
}

impl<Output, T, S> Serializer<Output, T> for &S where
    Output: OutputBuf,
    T: DeepView + ?Sized,
    S: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        (*self).exec_inv()
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        (*self).serialize_into(v, obuf)
    }
}

// pub trait ByteLen<Fmt> where
//     Self: DeepView,
//     Fmt: ValueByteLen<T = Self::V> + Consistency<Val = Self::V>,
//  {
//     fn byte_len_for(&self, binary_fmt: &Fmt) -> (len: usize)
//         requires
//             binary_fmt.consistent(self.deep_view()),
//             binary_fmt.byte_len(self.deep_view())
//                 <= usize::MAX,
//     // Fmt::value_byte_len(self.deep_view()) <= usize::MAX,
//         ensures
//             binary_fmt.consistent(self.deep_view()),
//             len == binary_fmt.byte_len(
//                 self.deep_view(),
//             ),
//     // len == Fmt::value_byte_len(self.deep_view()),
//     ;
// }
// impl ByteLen<U8> for u8 {
//     fn byte_len_for(&self, _binary_fmt: &U8) -> usize {
//         1
//     }
// }
// impl ByteLen<U16Be> for u16 {
//     fn byte_len_for(&self, _binary_fmt: &U16Be) -> usize {
//         2
//     }
// }
// impl ByteLen<U16Le> for u16 {
//     fn byte_len_for(&self, _binary_fmt: &U16Le) -> usize {
//         2
//     }
// }
// impl ByteLen<Const<U8, u8>> for u8 {
//     fn byte_len_for(&self, _binary_fmt: &Const<U8, u8>) -> usize {
//         1
//     }
// }
// impl<'x, const N: usize> ByteLen<Fixed<N>> for &'x [u8] {
//     fn byte_len_for(&self, _binary_fmt: &Fixed<N>) -> usize {
//         N
//     }
// }
// impl<'x, Len: AsLen> ByteLen<Varied<Len>> for &'x [u8] {
//     fn byte_len_for(&self, _binary_fmt: &Varied<Len>) -> usize {
//         self.len()
//     }
// }
// impl<FmtA, FmtB, A, B> ByteLen<Pair<FmtA, FmtB>> for (A, B) where
//     A: ByteLen<FmtA>,
//     B: ByteLen<FmtB>,
//     FmtA: ValueByteLen<T = A::V>,
//     FmtB: ValueByteLen<T = B::V>,
//  {
//     fn byte_len_for(&self, binary_fmt: &Pair<FmtA, FmtB>) -> usize {
//         self.0.byte_len_for(&binary_fmt.0) + self.1.byte_len_for(&binary_fmt.1)
//     }
// }
// // impl<FmtA, FmtB, A, B> ByteLen<Preceded<FmtA, A, FmtB>> for B where
// //     A: ByteLen<FmtA>,
// //     B: ByteLen<FmtB>,
// //     FmtA: ValueByteLen<T = A::V>,
// //     FmtB: ValueByteLen<T = B::V>,
// //  {
// //     fn byte_len_for(&self, binary_fmt: &Preceded<FmtA, A, FmtB>) -> usize {
// //         self.byte_len_for(&binary_fmt.b)
// //     }
// // }
// impl<FmtA, FmtB, A, B> ByteLen<Choice<FmtA, FmtB>> for Sum<A, B> where
//     A: ByteLen<FmtA>,
//     B: ByteLen<FmtB>,
//     FmtA: ValueByteLen<T = A::V>,
//     FmtB: ValueByteLen<T = B::V>,
//  {
//     fn byte_len_for(&self, binary_fmt: &Choice<FmtA, FmtB>) -> usize {
//         match self {
//             Sum::Inl(a) => a.byte_len_for(&binary_fmt.0),
//             Sum::Inr(b) => b.byte_len_for(&binary_fmt.1),
//         }
//     }
// }
// impl<Fmt, Predicate, T> ByteLen<Refined<Fmt, Predicate>> for T where
//     T: ByteLen<Fmt>,
//     Fmt: ValueByteLen<T = T::V>,
//     Predicate: Pred<T>,
//  {
//     fn byte_len_for(&self, binary_fmt: &Refined<Fmt, Predicate>) -> usize {
//         self.byte_len_for(&binary_fmt.0)
//     }
// }
// impl<Fmt, Map, T> ByteLen<Mapped<Fmt, Map>> for T where
//     T: DeepView<V = Map::Out>,
//     Fmt: ValueByteLen<T = Map::In>,
//     Map: for <'i>Mapper<&'i [u8], SOut = T>,
//     for <'i><Map as Mapper<&'i [u8]>>::SIn: ByteLen<Fmt>,
//  {
//     fn byte_len_for(&self, binary_fmt: &Mapped<Fmt, Map>) -> usize {
//         let mapped_in = Map::map_rev(self);
//         mapped_in.byte_len_for(&binary_fmt.inner)
//     }
// }
// #[verifier::allow_in_spec]
// pub fn small_nonzero(value: &u16) -> bool
//     returns
//         *value != 0,
// {
//     *value != 0
// }
// struct SmallNonZero;
// impl SpecPred<u16> for SmallNonZero {
//     open spec fn apply(&self, value: u16) -> bool {
//         small_nonzero(&value)
//     }
// }
// impl Pred<u16> for SmallNonZero {
//     fn test(&self, value: &u16) -> (ok: bool) {
//         small_nonzero(value)
//     }
// }
// pub struct Triple {
//     pub a: u8,
//     pub b: u16,
//     pub c: u8,
// }
// impl DeepView for Triple {
//     type V = Self;
//     open spec fn deep_view(&self) -> Self::V {
//         *self
//     }
// }
// pub struct TripleMapper;
// impl SpecMapper for TripleMapper {
//     type In = (u8, (u16, u8));
//     type Out = Triple;
//     open spec fn spec_map(i: Self::In) -> Self::Out {
//         Triple { a: i.0, b: i.1.0, c: i.1.1 }
//     }
//     open spec fn spec_map_rev(o: Self::Out) -> Self::In {
//         (o.a, (o.b, o.c))
//     }
// }
// impl Mapper<&[u8]> for TripleMapper {
//     type PIn = (u8, (u16, u8));
//     type POut = Triple;
//     type SIn = (u8, (u16, u8));
//     type SOut = Triple;
//     fn map(i: Self::PIn) -> Self::POut {
//         Triple { a: i.0, b: i.1.0, c: i.1.1 }
//     }
//     fn map_rev(o: &Self::SOut) -> Self::SIn {
//         (o.a, (o.b, o.c))
//     }
// }
// pub struct TrippleRefView {
//     pub a: u8,
//     pub b: u16,
//     pub c: Seq<u8>,
// }
// pub struct TripleRef<'i> {
//     pub a: u8,
//     pub b: u16,
//     pub c: &'i [u8],
// }
// impl DeepView for TripleRef<'_> {
//     type V = TrippleRefView;
//     open spec fn deep_view(&self) -> Self::V {
//         TrippleRefView { a: self.a, b: self.b, c: self.c.deep_view() }
//     }
// }
// pub struct TripleRefMapper;
// impl SpecMapper for TripleRefMapper {
//     type In = (u8, (u16, Seq<u8>));
//     type Out = TrippleRefView;
//     open spec fn spec_map(i: Self::In) -> Self::Out {
//         TrippleRefView { a: i.0, b: i.1.0, c: i.1.1 }
//     }
//     open spec fn spec_map_rev(o: Self::Out) -> Self::In {
//         (o.a, (o.b, o.c))
//     }
// }
// impl<'i> Mapper<&'i [u8]> for TripleRefMapper {
//     type PIn = (u8, (u16, &'i [u8]));
//     type POut = TripleRef<'i>;
//     type SIn = (u8, (u16, &'i [u8]));
//     type SOut = TripleRef<'i>;
//     fn map(i: Self::PIn) -> Self::POut {
//         TripleRef { a: i.0, b: i.1.0, c: i.1.1 }
//     }
//     fn map_rev(o: &Self::SOut) -> Self::SIn {
//         (o.a, (o.b, o.c))
//     }
// }
// fn test_fmt_len() {
//     // let x = (0u8, (2u16, 4u8));
//     // let my_fmt = Pair(U8, Pair(Refined(U16Le, SmallNonZero), U8));
//     // let x = Triple { a: 0u8, b: 2u16, c: 4u8 };
//     // let my_fmt = Mapped {
//     //     inner: Pair(U8, Pair(Refined(U16Le, SmallNonZero), U8)),
//     //     mapper: TripleMapper,
//     // };
//     let arr = [1u8, 0u8, 2u8, 4u8];
//     let x = TripleRef { a: 0u8, b: 2u16, c: &arr };
//     let my_fmt = Mapped {
//         inner: Pair(
//             Const(U8, 0),
//             Pair(Refined(U16Le, SmallNonZero), Fixed::<4>),
//         ),
//         mapper: TripleRefMapper,
//     };
//     let len = x.byte_len_for(&my_fmt);
//     assert(len == 1 + 2 + 4);
// }
// pub trait ByteLen<Fmt> where Self: DeepView, Fmt: ValueByteLen<T = Self::V>,  {
//     fn length(&self) -> (len: usize)
//         requires
//             Fmt::value_byte_len(self.deep_view()) <= usize::MAX,
//         ensures
//             len == Fmt::value_byte_len(self.deep_view()),
//     ;
// }
// use crate::combinators::{U8, U16Le, U16Be, Pair};
// impl ByteLen<U8> for u8 {
//     fn length(&self) -> usize {
//         1
//     }
// }
// impl ByteLen<U16Be> for u16 {
//     fn length(&self) -> usize {
//         2
//     }
// }
// impl ByteLen<U16Le> for u16 {
//     fn length(&self) -> usize {
//         2
//     }
// }
// impl<FmtA, FmtB, A, B> ByteLen<Pair<FmtA, FmtB>> for (A, B) where
//     A: ByteLen<FmtA>,
//     B: ByteLen<FmtB>,
//     FmtA: ValueByteLen<T = A::V>,
//     FmtB: ValueByteLen<T = B::V>,
//  {
//     fn length(&self) -> usize {
//         self.0.length() + self.1.length()
//     }
// }
// fn test_fmt_len() {
//     let x = (0u8, 0u16);
//     let len = <_ as ByteLen<Pair<U8, U16Le>>>::length(&x);
//     assert(len == 3);
// }
} // verus!
impl fmt::Display for ComplianceErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ComplianceErrorKind::LengthInconsistent => {
                f.write_str("value length does not match the format's declared length")
            }
            ComplianceErrorKind::InvalidTag => {
                f.write_str("value does not match the required tag or discriminant")
            }
            ComplianceErrorKind::PredicateFailed => {
                f.write_str("value failed a refinement predicate")
            }
            ComplianceErrorKind::CondRejected => {
                f.write_str("conditional format rejected this value")
            }
            ComplianceErrorKind::RecursionLimitExceeded => f.write_str("recursion limit exceeded"),
            ComplianceErrorKind::InvalidChoice => {
                f.write_str("value does not match any choice branch")
            }
            ComplianceErrorKind::Custom(s) => f.write_str(s),
        }
    }
}

impl fmt::Display for PreSerializeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PreSerializeErrorKind::LengthTooLarge => {
                f.write_str("computed encoded length exceeds usize::MAX")
            }
            PreSerializeErrorKind::NotCompliant(kind) => write!(f, "{}", kind),
        }
    }
}

impl fmt::Display for PreSerializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let format_trace = self.format_trace();
        if !format_trace.is_empty() {
            write!(f, "{} while preparing format stack ", self.kind)?;
            for (i, format_name) in format_trace.iter().rev().enumerate() {
                if i > 0 {
                    f.write_str(" -> ")?;
                }
                write!(f, "`{}`", format_name)?;
            }
            Ok(())
        } else {
            match self.failed_format {
                Some(current_format) => {
                    write!(
                        f,
                        "{} while preparing format `{}`",
                        self.kind, current_format
                    )
                }
                None => write!(f, "{}", self.kind),
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for PreSerializeError {}
