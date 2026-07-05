//! Executable serializer traits.
use crate::core::spec::{Consistency, SpecByteLen, SpecSerializer};
use core::fmt;
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use vstd::prelude::*;

verus! {

pub trait Serializer<T> where
    Self: SpecSerializer<SVal = T::V> + Consistency<Val = T::V>,
    T: DeepView + ?Sized,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn serialize(&self, v: &T, obuf: &mut Vec<u8>)
        requires
            self.exec_inv(),
            self.consistent(v.deep_view()),
        ensures
            final(obuf)@ == old(obuf)@ + self.spec_serialize(v.deep_view()),
    ;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ComplianceErrorKind {
    LengthInconsistent,
    InvalidTag,
    PredicateFailed,
    CondRejected,
    RecursionLimitExceeded,
    InvalidChoice,
    Custom(&'static str),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum PreSerializeErrorKind {
    LengthTooLarge,
    NotCompliant(ComplianceErrorKind),
}

#[derive(Debug, PartialEq, Eq)]
pub struct PreSerializeError {
    pub kind: PreSerializeErrorKind,
    pub failed_format: Option<&'static str>,
    #[cfg(feature = "alloc")]
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
    pub fn new(kind: PreSerializeErrorKind) -> Self {
        Self {
            kind,
            failed_format: None,
            #[cfg(feature = "alloc")]
            format_stack: Vec::new(),
        }
    }

    pub fn length_too_large() -> Self {
        Self::new(PreSerializeErrorKind::LengthTooLarge)
    }

    pub fn not_compliant(kind: ComplianceErrorKind) -> Self {
        Self::new(PreSerializeErrorKind::NotCompliant(kind))
    }

    pub fn custom(msg: &'static str) -> Self {
        Self::new(PreSerializeErrorKind::NotCompliant(ComplianceErrorKind::Custom(msg)))
    }

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

    pub fn failed_format(&self) -> Option<&'static str> {
        self.failed_format
    }

    pub fn format_trace(&self) -> &[&'static str] {
        #[cfg(feature = "alloc")]
        { self.format_stack.as_slice() }
        #[cfg(not(feature = "alloc"))]
        { &[] }
    }
}

pub trait Prepare<T>: SpecByteLen<T = T::V> + Consistency<Val = T::V> where T: DeepView + ?Sized {
    open spec fn exec_inv(&self) -> bool {
        true
    }

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

pub trait ByteLen<T>: SpecByteLen<T = T::V> where T: DeepView + ?Sized {
    open spec fn exec_inv(&self) -> bool {
        true
    }

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

impl<S: Consistency> Consistency for &S {
    type Val = S::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (*self).consistent(v)
    }
}

impl<T, S> Serializer<T> for &S where T: DeepView, S: Serializer<T> {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        (*self).exec_inv()
    }

    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        (*self).serialize(v, obuf)
    }
}

// pub trait Serializer: ExSerializer + Consistency<Val = Self::SVal> + SpecByteLen<T = Self::SVal> {
//     fn serialize(&self, v: &Self::ST, obuf: &mut Vec<u8>)
//         requires
//             self.exec_inv(),
//             self.consistent(v.deep_view()),
//         ensures
//             final(obuf).len() == old(obuf).len() + self.byte_len(v.deep_view()),
//             final(obuf)@ == old(obuf)@ + self.spec_serialize(v.deep_view()),
//     ;
// }
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
// /// For serializers, we prefer to use trait generics instead of associated types, since it allows for the same serializer
// /// combinator to be used for multiple types (e.g., borrowed vs owned).
// pub trait Serializer<T>: Consistency + SpecSerializer<SVal = Self::Val> where
//     T: DeepView<V = Self::Val>,
//  {
//     open spec fn exec_inv(&self) -> bool {
//         true
//     }
//     fn serialize(&self, v: &T, obuf: &mut Vec<u8>) -> (len: usize);
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
