#![allow(rustdoc::broken_intra_doc_links)]
use crate::properties::*;
use vstd::prelude::*;

use super::bytes::Variable;

verus! {

/// Spec version of [`Iso`].
pub trait SpecIso {
    /// The source type of the isomorphism.
    type Src: SpecFrom<Self::Dst>;

    /// The destination type of the isomorphism.
    type Dst: SpecFrom<Self::Src>;
}

/// The bijective functions of [`SpecIso`]
pub trait SpecIsoFn: SpecIso {
    /// Applies the isomorphism to the source type.
    spec fn spec_apply(s: Self::Src) -> Self::Dst;

    /// Applies the reverse isomorphism to the destination type.
    spec fn spec_rev_apply(s: Self::Dst) -> Self::Src;
}

// Blanket implementation for all types that implement `SpecIso`
impl<T: SpecIso> SpecIsoFn for T {
    open spec fn spec_apply(s: Self::Src) -> Self::Dst {
        <Self::Dst as SpecFrom<Self::Src>>::spec_from(s)
    }

    open spec fn spec_rev_apply(s: Self::Dst) -> Self::Src {
        <Self::Src as SpecFrom<Self::Dst>>::spec_from(s)
    }
}

/// The proof of [`SpecIsoFn`]
pub trait SpecIsoProof: SpecIsoFn {
    /// One direction of the isomorphism.
    proof fn spec_iso(s: Self::Src)
        ensures
            Self::spec_rev_apply(Self::spec_apply(s)) == s,
    ;

    /// The other direction of the isomorphism.
    proof fn spec_iso_rev(s: Self::Dst)
        ensures
            Self::spec_apply(Self::spec_rev_apply(s)) == s,
    ;
}

/// All isomorphisms to be used in [`Mapped`] combinator must implement this trait.
pub trait Iso: View where
    Self::V: SpecIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecFrom<<Self::Src as View>::V>,
 {
    /// The source type of the isomorphism.
    type Src: View;

    /// The reference of the [`Src`] type.
    type RefSrc<'a>: View<V = <Self::Src as View>::V> + From<&'a Self::Dst> where Self::Dst: 'a;

    /// The destination type of the isomorphism.
    type Dst: View + From<Self::Src>;
}

/// The bijective functions of [`Iso`]
/// [`Self::apply`] and [`Self::rev_apply`] must be inverses of each other.
/// See [`SpecIsoFn::spec_iso`] and [`SpecIsoFn::spec_iso_rev`] for more details.
pub trait IsoFn: Iso where
    Self::V: SpecIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecFrom<<Self::Src as View>::V>,
 {
    /// Applies the isomorphism to the source type.
    fn apply(s: Self::Src) -> (res: Self::Dst)
        ensures
            res@ == Self::V::spec_apply(s@),
    ;

    /// Applies the reverse isomorphism to the destination type.
    fn rev_apply<'a>(s: &'a Self::Dst) -> (res: Self::RefSrc<'a>)
        ensures
            res@ == Self::V::spec_rev_apply(s@),
    ;
}

// Blanket implementation for all types that implement `Iso`
impl<T: Iso> IsoFn for T where
    T::V: SpecIso<Src = <T::Src as View>::V, Dst = <T::Dst as View>::V>,
    <T::Src as View>::V: SpecFrom<<T::Dst as View>::V>,
    <T::Dst as View>::V: SpecFrom<<T::Src as View>::V>,
 {
    fn apply(s: Self::Src) -> (res: Self::Dst) {
        Self::Dst::ex_from(s)
    }

    fn rev_apply(s: Self::Dst) -> (res: Self::Src) {
        Self::Src::ex_from(s)
    }
}

/// Combinator that maps the result of an `inner` combinator with an isomorphism that implements
/// [`Iso`].
pub struct Mapped<Inner, M> {
    /// The inner combinator.
    pub inner: Inner,
    /// The isomorphism.
    pub mapper: M,
}

impl<Inner: View, M: View> View for Mapped<Inner, M> {
    type V = Mapped<Inner::V, M::V>;

    open spec fn view(&self) -> Self::V {
        Mapped { inner: self.inner@, mapper: self.mapper@ }
    }
}

impl<Inner, M> SpecCombinator for Mapped<Inner, M> where
    Inner: SpecCombinator,
    M: SpecIso<Src = Inner::Type>,
    Inner::Type: SpecFrom<M::Dst>,
    M::Dst: SpecFrom<Inner::Type>,
 {
    type Type = M::Dst;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        match self.inner.spec_parse(s) {
            Err(e) => Err(e),
            Ok((n, v)) => Ok((n, M::spec_apply(v))),
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.inner.spec_serialize(M::spec_rev_apply(v))
    }
}

impl<Inner, M> SecureSpecCombinator for Mapped<Inner, M> where
    Inner: SecureSpecCombinator,
    M: SpecIsoProof<Src = Inner::Type>,
    Inner::Type: SpecFrom<M::Dst>,
    M::Dst: SpecFrom<Inner::Type>,
 {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.inner.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(buf) = self.inner.spec_serialize(M::spec_rev_apply(v)) {
            M::spec_iso_rev(v);
            self.inner.theorem_serialize_parse_roundtrip(M::spec_rev_apply(v))
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.lemma_parse_length(buf);
        self.inner.theorem_parse_serialize_roundtrip(buf);
        if let Ok((n, v)) = self.inner.spec_parse(buf) {
            M::spec_iso(v)
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        if let Ok((n, v)) = self.inner.spec_parse(s1) {
            self.inner.lemma_parse_length(s1);
            M::spec_iso(v)
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.inner.lemma_parse_length(s);
        if let Ok((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.inner.lemma_parse_productive(s);
        if let Ok((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }
}

impl<I, O, Inner, M> Combinator<I, O> for Mapped<Inner, M> where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V>,
    M: Iso<Src = Inner::Type>,
    Inner::Type: From<M::Dst> + View,
    M::Dst: From<Inner::Type> + View,
    M::V: SpecIsoProof<Src = <Inner::Type as View>::V, Dst = <M::Dst as View>::V>,
    <Inner::Type as View>::V: SpecFrom<<M::Dst as View>::V>,
    <M::Dst as View>::V: SpecFrom<<Inner::Type as View>::V>,
 {
    type Type = M::Dst;

    type SType<'a> = &'a M::Dst where <M as Iso>::Dst: 'a;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        match self.inner.parse(s) {
            Err(e) => Err(e),
            Ok((n, v)) => {
                proof {
                    M::V::spec_iso(v@);
                }
                Ok((n, M::apply(v)))
            },
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize<'a>(&self, v: Self::SType<'a>, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        self.inner.serialize(M::rev_apply(v), data, pos)
    }
}

/// Spec version of [`PartialIso`].
pub trait SpecPartialIso {
    /// The source type
    type Src: SpecTryFrom<Self::Dst>;

    /// The destination type
    type Dst: SpecTryFrom<Self::Src>;
}

/// The faillible functions of [`SpecPartialIso`]
pub trait SpecPartialIsoFn: SpecPartialIso {
    /// Applies the faillible conversion to the source type.
    spec fn spec_apply(s: Self::Src) -> Result<
        Self::Dst,
        <Self::Dst as SpecTryFrom<Self::Src>>::Error,
    >;

    /// Applies the reverse faillible conversion to the destination type.
    spec fn spec_rev_apply(s: Self::Dst) -> Result<
        Self::Src,
        <Self::Src as SpecTryFrom<Self::Dst>>::Error,
    >;
}

// Blanket implementation for all types that implement `SpecPartialIso`
impl<T: SpecPartialIso> SpecPartialIsoFn for T {
    open spec fn spec_apply(s: Self::Src) -> Result<
        Self::Dst,
        <Self::Dst as SpecTryFrom<Self::Src>>::Error,
    > {
        Self::Dst::spec_try_from(s)
    }

    open spec fn spec_rev_apply(s: Self::Dst) -> Result<
        Self::Src,
        <Self::Src as SpecTryFrom<Self::Dst>>::Error,
    > {
        Self::Src::spec_try_from(s)
    }
}

/// The proof of [`SpecPartialIsoFn`]
pub trait SpecPartialIsoProof: SpecPartialIsoFn {
    /// One direction of the isomorphism when the conversion is successful.
    proof fn spec_iso(s: Self::Src)
        ensures
            Self::spec_apply(s) matches Ok(v) ==> {
                &&& Self::spec_rev_apply(v) is Ok
                &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
            },
    ;

    /// The other direction of the isomorphism when the conversion is successful.
    proof fn spec_iso_rev(s: Self::Dst)
        ensures
            Self::spec_rev_apply(s) matches Ok(v) ==> {
                &&& Self::spec_apply(v) is Ok
                &&& Self::spec_apply(v) matches Ok(s_) && s == s_
            },
    ;
}

/// Faillible version of [`Iso`].
pub trait PartialIso: View where
    Self::V: SpecPartialIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecTryFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecTryFrom<<Self::Src as View>::V>,
 {
    /// The source type
    type Src: View + TryFrom<Self::Dst>;

    /// The destination type
    type Dst: View + TryFrom<Self::Src>;
}

/// The faillible functions of [`PartialIso`]
pub trait PartialIsoFn: PartialIso where
    Self::V: SpecPartialIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecTryFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecTryFrom<<Self::Src as View>::V>,
 {
    /// Applies the faillible conversion to the source type.
    fn apply(s: Self::Src) -> (res: Result<Self::Dst, <Self::Dst as TryFrom<Self::Src>>::Error>)
        ensures
            res matches Ok(v) ==> {
                &&& Self::V::spec_apply(s@) is Ok
                &&& Self::V::spec_apply(s@) matches Ok(v_) && v@ == v_
            },
            res matches Err(e) ==> Self::V::spec_apply(s@) is Err,
    ;

    /// Applies the reverse faillible conversion to the destination type.
    fn rev_apply(s: Self::Dst) -> (res: Result<Self::Src, <Self::Src as TryFrom<Self::Dst>>::Error>)
        ensures
            res matches Ok(v) ==> {
                &&& Self::V::spec_rev_apply(s@) is Ok
                &&& Self::V::spec_rev_apply(s@) matches Ok(v_) && v@ == v_
            },
            res matches Err(e) ==> Self::V::spec_rev_apply(s@) is Err,
    ;
}

// Blanket implementation for all types that implement `PartialIso`
impl<T: PartialIso> PartialIsoFn for T where
    T::V: SpecPartialIso<Src = <T::Src as View>::V, Dst = <T::Dst as View>::V>,
    <T::Src as View>::V: SpecTryFrom<<T::Dst as View>::V>,
    <T::Dst as View>::V: SpecTryFrom<<T::Src as View>::V>,
 {
    fn apply(s: Self::Src) -> (res: Result<Self::Dst, <Self::Dst as TryFrom<Self::Src>>::Error>) {
        Self::Dst::ex_try_from(s)
    }

    fn rev_apply(s: Self::Dst) -> (res: Result<
        Self::Src,
        <Self::Src as TryFrom<Self::Dst>>::Error,
    >) {
        Self::Src::ex_try_from(s)
    }
}

/// Combinator that maps the result of an `inner` combinator with a faillible conversion
/// that implements [`TryFromInto`].
pub struct TryMap<Inner, M> {
    /// The inner combinator.
    pub inner: Inner,
    /// The faillible conversion.
    pub mapper: M,
}

impl<Inner: View, M: View> View for TryMap<Inner, M> {
    type V = TryMap<Inner::V, M::V>;

    open spec fn view(&self) -> Self::V {
        TryMap { inner: self.inner@, mapper: self.mapper@ }
    }
}

impl<Inner, M> SpecCombinator for TryMap<Inner, M> where
    Inner: SpecCombinator,
    M: SpecPartialIso<Src = Inner::Type>,
    Inner::Type: SpecTryFrom<M::Dst>,
    M::Dst: SpecTryFrom<Inner::Type>,
 {
    type Type = M::Dst;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        match self.inner.spec_parse(s) {
            Err(e) => Err(e),
            Ok((n, v)) => match M::spec_apply(v) {
                Ok(v) => Ok((n, v)),
                Err(_) => Err(()),
            },
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        match M::spec_rev_apply(v) {
            Ok(v) => self.inner.spec_serialize(v),
            Err(_) => Err(()),
        }
    }
}

impl<Inner, M> SecureSpecCombinator for TryMap<Inner, M> where
    Inner: SecureSpecCombinator,
    M: SpecPartialIsoProof<Src = Inner::Type>,
    Inner::Type: SpecTryFrom<M::Dst>,
    M::Dst: SpecTryFrom<Inner::Type>,
 {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.inner.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(v_) = M::spec_rev_apply(v) {
            M::spec_iso_rev(v);
            self.inner.theorem_serialize_parse_roundtrip(v_);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.lemma_parse_length(buf);
        self.inner.theorem_parse_serialize_roundtrip(buf);
        if let Ok((n, v)) = self.inner.spec_parse(buf) {
            M::spec_iso(v)
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        if let Ok((n, v)) = self.inner.spec_parse(s1) {
            self.inner.lemma_parse_length(s1);
            M::spec_iso(v)
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.inner.lemma_parse_length(s);
        if let Ok((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.inner.lemma_parse_productive(s);
        if let Ok((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }
}

impl<I, O, Inner, M> Combinator<I, O> for TryMap<Inner, M> where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V>,
    M: PartialIso<Src = Inner::Type>,
    Inner::Type: TryFrom<M::Dst> + View,
    M::Dst: TryFrom<Inner::Type> + View,
    M::V: SpecPartialIsoProof<Src = <Inner::Type as View>::V, Dst = <M::Dst as View>::V>,
    <Inner::Type as View>::V: SpecTryFrom<<M::Dst as View>::V>,
    <M::Dst as View>::V: SpecTryFrom<<Inner::Type as View>::V>,
 {
    type Type = M::Dst;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        match self.inner.parse(s) {
            Err(e) => Err(e),
            Ok((n, v)) => match M::apply(v) {
                Ok(v) => Ok((n, v)),
                Err(_) => Err(ParseError::TryMapFailed),
            },
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        match M::rev_apply(v) {
            Ok(v) => self.inner.serialize(v, data, pos),
            Err(_) => Err(SerializeError::TryMapFailed),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::uints::*;

    verus! {

// exhaustive enum

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub enum FieldLess {
    A = 0,
    B = 1,
    C = 2,
}

pub type FieldLessInner = u8;

impl View for FieldLess {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Compare<FieldLess> for FieldLess {
    fn compare(&self, other: &FieldLess) -> bool {
        *self == *other
    }
}
impl SpecTryFrom<FieldLessInner> for FieldLess {
    type Error = ();

    open spec fn spec_try_from(v: FieldLessInner) -> Result<FieldLess, ()> {
        match v {
            0u8 => Ok(FieldLess::A),
            1u8 => Ok(FieldLess::B),
            2u8 => Ok(FieldLess::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<FieldLess> for FieldLessInner {
    type Error = ();

    open spec fn spec_try_from(v: FieldLess) -> Result<FieldLessInner, ()> {
        match v {
            FieldLess::A => Ok(0u8),
            FieldLess::B => Ok(1u8),
            FieldLess::C => Ok(2u8),
        }
    }
}

impl TryFrom<FieldLessInner> for FieldLess {
    type Error = ();

    fn ex_try_from(v: FieldLessInner) -> Result<FieldLess, ()> {
        match v {
            0u8 => Ok(FieldLess::A),
            1u8 => Ok(FieldLess::B),
            2u8 => Ok(FieldLess::C),
            _ => Err(()),
        }
    }
}

impl TryFrom<FieldLess> for FieldLessInner {
    type Error = ();

    fn ex_try_from(v: FieldLess) -> Result<FieldLessInner, ()> {
        match v {
            FieldLess::A => Ok(0u8),
            FieldLess::B => Ok(1u8),
            FieldLess::C => Ok(2u8),
        }
    }
}

struct FieldLessMapper;

impl View for FieldLessMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for FieldLessMapper {
    type Src = FieldLessInner;
    type Dst = FieldLess;
}

impl SpecPartialIsoProof for FieldLessMapper {
    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl PartialIso for FieldLessMapper {
    type Src = FieldLessInner;
    type Dst = FieldLess;
}

type FieldLessCombinator = TryMap<U8, FieldLessMapper>;

spec fn spec_field_less() -> FieldLessCombinator {
    TryMap { inner: U8, mapper: FieldLessMapper }
}

fn field_less() -> (o: FieldLessCombinator)
    ensures o@ == spec_field_less(),
{
    TryMap { inner: U8, mapper: FieldLessMapper }
}

spec fn parse_spec_field_less(i: Seq<u8>) -> Result<(usize, FieldLess), ()> {
    spec_field_less().spec_parse(i)
}

spec fn serialize_spec_field_less(msg: FieldLess) -> Result<Seq<u8>, ()> {
    spec_field_less().spec_serialize(msg)
}

fn parse_field_less(i: &[u8]) -> (o: Result<(usize, FieldLess), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_field_less(i@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&field_less(), i)
}

fn serialize_field_less(msg: FieldLess, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_field_less(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    <_ as Combinator<&[u8], Vec<u8>>>::serialize(&field_less(), msg, data, pos)
}

// non-exhaustive enum
// NOTE: It turns out that the following encoding creates an anbiguous format, e.g. both
// `NonExhaustive::X` and `NonExhaustive::Unknown(0)` would be serialized to `0x00`, which could
// lead to format confusion attacks (though it's not immediately clear how). Interestingly,
// [rustls](https://github.com/rustls/rustls/blob/main/rustls/src/msgs/macros.rs#L68) uses a
// similar encoding for all its enums.
//
// For security, we should just use primitive uint combinators for non-exhaustive enums.

// #[non_exhaustive]
// #[repr(u8)]
// pub enum NonExhaustive {
//     X = 0,
//     Y = 1,
//     Z = 2,
//     Unknown(u8),
// }
//
// pub type NonExhaustiveInner = u8;
//
// impl View for NonExhaustive {
//     type V = Self;
//
//     open spec fn view(&self) -> Self::V {
//         *self
//     }
// }
//
// impl SpecFrom<NonExhaustiveInner> for NonExhaustive {
//     open spec fn spec_from(v: NonExhaustiveInner) -> NonExhaustive {
//         match v {
//             0u8 => NonExhaustive::X,
//             1u8 => NonExhaustive::Y,
//             2u8 => NonExhaustive::Z,
//             _ => NonExhaustive::Unknown(v),
//         }
//     }
// }
//
// impl SpecFrom<NonExhaustive> for NonExhaustiveInner {
//     open spec fn spec_from(v: NonExhaustive) -> NonExhaustiveInner {
//         match v {
//             NonExhaustive::X => 0u8,
//             NonExhaustive::Y => 1u8,
//             NonExhaustive::Z => 2u8,
//             NonExhaustive::Unknown(v) => v,
//         }
//     }
// }
//
// impl From<NonExhaustiveInner> for NonExhaustive {
//     fn ex_from(v: NonExhaustiveInner) -> NonExhaustive {
//         match v {
//             0u8 => NonExhaustive::X,
//             1u8 => NonExhaustive::Y,
//             2u8 => NonExhaustive::Z,
//             _ => NonExhaustive::Unknown(v),
//         }
//     }
// }
//
// impl From<NonExhaustive> for NonExhaustiveInner {
//     fn ex_from(v: NonExhaustive) -> NonExhaustiveInner {
//         match v {
//             NonExhaustive::X => 0u8,
//             NonExhaustive::Y => 1u8,
//             NonExhaustive::Z => 2u8,
//             NonExhaustive::Unknown(v) => v,
//         }
//     }
// }
//
// struct NonExhaustiveMapper;
//
// impl View for NonExhaustiveMapper {
//     type V = Self;
//
//     open spec fn view(&self) -> Self::V {
//         *self
//     }
// }
//
// impl SpecIso for NonExhaustiveMapper {
//     type Src = NonExhaustiveInner;
//     type Dst = NonExhaustive;
//
//     proof fn spec_iso(s: Self::Src) {
//     }
//
//     proof fn spec_iso_rev(s: Self::Dst) {
//         // would fail because of the ambiguity in the encoding
//     }
// }
//
// impl Iso for NonExhaustiveMapper {
//     type Src = NonExhaustiveInner;
//     type Dst = NonExhaustive;
//
//     type Src = NonExhaustiveInner;
//     type Dst = NonExhaustive;
// }
}

}

/// The spec version of [`Pred`].
pub trait SpecPred {
    /// The input type of the predicate.
    type Input;

    /// Applies the predicate to the input.
    spec fn spec_apply(&self, i: &Self::Input) -> bool;
}

/// All predicates to be used in [`Refined`] combinator must implement this trait.
pub trait Pred: View where Self::V: SpecPred<Input = <Self::Input as View>::V> {
    /// The input type of the predicate.
    type Input: View + ?Sized;

    /// Applies the predicate to the input.
    fn apply(&self, i: &Self::Input) -> (res: bool)
        ensures
            res == self@.spec_apply(&i@),
    ;
}

/// Combinator that refines the result of an `inner` combinator with a predicate that implements
/// [`Pred`].
pub struct Refined<Inner, P> {
    /// The inner combinator.
    pub inner: Inner,
    /// The predicate.
    pub predicate: P,
}

impl<Inner: View, P: View> View for Refined<Inner, P> where  {
    type V = Refined<Inner::V, P::V>;

    open spec fn view(&self) -> Self::V {
        Refined { inner: self.inner@, predicate: self.predicate@ }
    }
}

impl<Inner, P> SpecCombinator for Refined<Inner, P> where
    Inner: SpecCombinator,
    P: SpecPred<Input = Inner::Type>,
 {
    type Type = Inner::Type;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        match self.inner.spec_parse(s) {
            Ok((n, v)) if self.predicate.spec_apply(&v) => Ok((n, v)),
            _ => Err(()),
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if self.predicate.spec_apply(&v) {
            self.inner.spec_serialize(v)
        } else {
            Err(())
        }
    }
}

impl<Inner, P> SecureSpecCombinator for Refined<Inner, P> where
    Inner: SecureSpecCombinator,
    P: SpecPred<Input = Inner::Type>,
 {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.inner.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.inner.theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        assert(Self::is_prefix_secure() ==> self.spec_parse(s1).is_ok() ==> self.spec_parse(
            s1.add(s2),
        ) == self.spec_parse(s1));
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.inner.lemma_parse_length(s);
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.inner.lemma_parse_productive(s);
    }
}

impl<I, O, Inner, P> Combinator<I, O> for Refined<Inner, P> where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V>,
    P: Pred<Input = Inner::Type>,
    P::V: SpecPred<Input = <Inner::Type as View>::V>,
 {
    type Type = Inner::Type;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        match self.inner.parse(s) {
            Ok((n, v)) => if self.predicate.apply(&v) {
                Ok((n, v))
            } else {
                Err(ParseError::RefinedPredicateFailed)
            },
            Err(e) => Err(e),
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        if self.predicate.apply(&v) {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::RefinedPredicateFailed)
        }
    }
}

/// Combinator that checks if `cond` is true and then delegates to the `inner` combinator.
pub struct Cond<Inner> {
    /// The condition to check before parsing or serializing.
    pub cond: bool,
    /// The combinator to delegate to if `cond` is true.
    pub inner: Inner,
}

impl<Inner: View> View for Cond<Inner> {
    type V = Cond<Inner::V>;

    open spec fn view(&self) -> Self::V {
        Cond { cond: self.cond, inner: self.inner@ }
    }
}

impl<Inner: SpecCombinator> SpecCombinator for Cond<Inner> {
    type Type = Inner::Type;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if self.cond {
            self.inner.spec_parse(s)
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if self.cond {
            self.inner.spec_serialize(v)
        } else {
            Err(())
        }
    }
}

impl<Inner: SecureSpecCombinator> SecureSpecCombinator for Cond<Inner> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if self.cond {
            self.inner.theorem_serialize_parse_roundtrip(v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if self.cond {
            self.inner.theorem_parse_serialize_roundtrip(buf);
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.cond {
            self.inner.lemma_prefix_secure(s1, s2);
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if self.cond {
            self.inner.lemma_parse_length(s);
        }
    }

    open spec fn is_productive(&self) -> bool {
        self.inner.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.inner.lemma_parse_productive(s);
    }
}

impl<I: VestInput, O: VestOutput<I>, Inner: Combinator<I, O>> Combinator<I, O> for Cond<
    Inner,
> where Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V> {
    type Type = Inner::Type;

    open spec fn spec_length(&self) -> Option<usize> {
        if self.cond@ {
            self.inner.spec_length()
        } else {
            None
        }
    }

    fn length(&self) -> Option<usize> {
        if self.cond {
            self.inner.length()
        } else {
            None
        }
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if self.cond {
            self.inner.parse(s)
        } else {
            Err(ParseError::CondFailed)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        if self.cond {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::CondFailed)
        }
    }
}


/// Combinator that monadically chains two combinators.
pub struct AndThen<Prev, Next>(pub Prev, pub Next);

impl<Prev: View, Next: View> View for AndThen<Prev, Next> {
    type V = AndThen<Prev::V, Next::V>;

    open spec fn view(&self) -> Self::V {
        AndThen(self.0@, self.1@)
    }
}

impl<Next: SpecCombinator> SpecCombinator for AndThen<Variable, Next> {
    type Type = Next::Type;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if let Ok((n, v1)) = self.0.spec_parse(s) {
            if let Ok((m, v2)) = self.1.spec_parse(v1) {
                // !! for security, can only proceed if the `Next` parser consumed the entire
                // !! output from the `Prev` parser
                if m == n {
                    Ok((n, v2))
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if let Ok(buf1) = self.1.spec_serialize(v) {
            self.0.spec_serialize(buf1)
        } else {
            Err(())
        }
    }
}

impl<Next: SecureSpecCombinator> SecureSpecCombinator for AndThen<Variable, Next> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(buf1) = self.1.spec_serialize(v) {
            self.1.theorem_serialize_parse_roundtrip(v);
            self.0.theorem_serialize_parse_roundtrip(buf1);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v1)) = self.0.spec_parse(buf) {
            if let Ok((m, v2)) = self.1.spec_parse(v1) {
                self.0.theorem_parse_serialize_roundtrip(buf);
                self.1.theorem_parse_serialize_roundtrip(v1);
                if m == n {
                    if let Ok(buf2) = self.1.spec_serialize(v2) {
                        if let Ok(buf1) = self.0.spec_serialize(buf2) {
                            assert(buf1 == buf.subrange(0, n as int));
                        }
                    }
                }
            }
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Variable::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(buf, s2);
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Ok((n, v1)) = self.0.spec_parse(s) {
            self.0.lemma_parse_length(s);
            self.1.lemma_parse_length(v1);
        }
    }

    open spec fn is_productive(&self) -> bool {
        self.0.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I, O, Next: Combinator<I, O>> Combinator<I, O> for AndThen<Variable, Next> where
    I: VestInput,
    O: VestOutput<I>,
    Next::V: SecureSpecCombinator<Type = <Next::Type as View>::V>,
 {
    type Type = Next::Type;

    open spec fn spec_length(&self) -> Option<usize> {
        // self.0.spec_length()
        <_ as Combinator<I, O>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        // self.0.length()
        <_ as Combinator<I, O>>::length(&self.0)
    }

    open spec fn parse_requires(&self) -> bool {
        self.1.parse_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v1) = <_ as Combinator<I, O>>::parse(&self.0, s)?;
        let (m, v2) = self.1.parse(v1)?;
        if m == n {
            Ok((n, v2))
        } else {
            Err(ParseError::AndThenUnusedBytes)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.1.serialize_requires()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        let n = self.1.serialize(v, data, pos)?;
        if n == self.0.0 {
            Ok(n)
        } else {
            Err(SerializeError::AndThenUnusedBytes)
        }
    }
}

} // verus!
