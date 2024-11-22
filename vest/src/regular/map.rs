#![allow(rustdoc::broken_intra_doc_links)]
use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Spec version of [`Iso`].
/// It mandates that the isomorphism is bijective.
pub trait SpecIso {
    /// The source type of the isomorphism.
    type Src: SpecFrom<Self::Dst>;

    /// The destination type of the isomorphism.
    type Dst: SpecFrom<Self::Src>;

    /// Applies the isomorphism to the source type.
    open spec fn spec_apply(s: Self::Src) -> Self::Dst {
        Self::Dst::spec_from(s)
    }

    /// Applies the reverse isomorphism to the destination type.
    open spec fn spec_rev_apply(s: Self::Dst) -> Self::Src {
        Self::Src::spec_from(s)
    }

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
/// [`Self::apply`] and [`Self::rev_apply`] must be inverses of each other.
/// See [`SpecIso::spec_iso`] and [`SpecIso::spec_iso_rev`] for more details.
pub trait Iso: View where
    Self::V: SpecIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecFrom<<Self::Src as View>::V>,
 {
    /// The source type of the isomorphism.
    type Src: View + From<Self::Dst>;

    /// The destination type of the isomorphism.
    type Dst: View + From<Self::Src>;

    /// Applies the isomorphism to the source type.
    fn apply(s: Self::Src) -> (res: Self::Dst)
        ensures
            res@ == Self::V::spec_apply(s@),
    {
        assert(Self::V::spec_apply(s@) == <Self::Dst as View>::V::spec_from(s@)) by (compute_only);
        Self::Dst::ex_from(s)
    }

    /// Applies the reverse isomorphism to the destination type.
    fn rev_apply(s: Self::Dst) -> (res: Self::Src)
        ensures
            res@ == Self::V::spec_rev_apply(s@),
    {
        assert(Self::V::spec_rev_apply(s@) == <Self::Src as View>::V::spec_from(s@))
            by (compute_only);
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
    M: SpecIso<Src = Inner::SpecResult>,
    Inner::SpecResult: SpecFrom<M::Dst>,
    M::Dst: SpecFrom<Inner::SpecResult>,
 {
    type SpecResult = M::Dst;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match self.inner.spec_parse(s) {
            Err(e) => Err(e),
            Ok((n, v)) => Ok((n, M::spec_apply(v))),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.inner.spec_parse_wf(s);
        if let Ok((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.inner.spec_serialize(M::spec_rev_apply(v))
    }
}

impl<Inner, M> SecureSpecCombinator for Mapped<Inner, M> where
    Inner: SecureSpecCombinator,
    M: SpecIso<Src = Inner::SpecResult>,
    Inner::SpecResult: SpecFrom<M::Dst>,
    M::Dst: SpecFrom<Inner::SpecResult>,
 {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(buf) = self.inner.spec_serialize(M::spec_rev_apply(v)) {
            M::spec_iso_rev(v);
            self.inner.theorem_serialize_parse_roundtrip(M::spec_rev_apply(v))
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.spec_parse_wf(buf);
        self.inner.theorem_parse_serialize_roundtrip(buf);
        if let Ok((n, v)) = self.inner.spec_parse(buf) {
            M::spec_iso(v)
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        if let Ok((n, v)) = self.inner.spec_parse(s1) {
            self.inner.spec_parse_wf(s1);
            M::spec_iso(v)
        }
    }
}

impl<I, O, Inner, M> Combinator<I, O> for Mapped<Inner, M> where
    I: VestSecretInput,
    O: VestSecretOutput<I>,
    Inner: Combinator<I, O>,
    Inner::V: SecureSpecCombinator<SpecResult = <Inner::Result as View>::V>,
    M: Iso<Src = Inner::Result>,
    Inner::Result: From<M::Dst> + View,
    M::Dst: From<Inner::Result> + View,
    M::V: SpecIso<Src = <Inner::Result as View>::V, Dst = <M::Dst as View>::V>,
    <Inner::Result as View>::V: SpecFrom<<M::Dst as View>::V>,
    <M::Dst as View>::V: SpecFrom<<Inner::Result as View>::V>,
 {
    type Result = M::Dst;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Result), ParseError>) {
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

    fn serialize(&self, v: Self::Result, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        self.inner.serialize(M::rev_apply(v), data, pos)
    }
}

/// Spec version of [`TryFromInto`].
pub trait SpecTryFromInto {
    /// The source type
    type Src: SpecTryFrom<Self::Dst>;

    /// The destination type
    type Dst: SpecTryFrom<Self::Src>;

    /// Applies the faillible conversion to the source type.
    open spec fn spec_apply(s: Self::Src) -> Result<
        Self::Dst,
        <Self::Dst as SpecTryFrom<Self::Src>>::Error,
    > {
        Self::Dst::spec_try_from(s)
    }

    /// Applies the reverse faillible conversion to the destination type.
    open spec fn spec_rev_apply(s: Self::Dst) -> Result<
        Self::Src,
        <Self::Src as SpecTryFrom<Self::Dst>>::Error,
    > {
        Self::Src::spec_try_from(s)
    }

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
pub trait TryFromInto: View where
    Self::V: SpecTryFromInto<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecTryFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecTryFrom<<Self::Src as View>::V>,
 {
    /// The source type
    type Src: View + TryFrom<Self::Dst>;

    /// The destination type
    type Dst: View + TryFrom<Self::Src>;

    /// Applies the faillible conversion to the source type.
    fn apply(s: Self::Src) -> (res: Result<Self::Dst, <Self::Dst as TryFrom<Self::Src>>::Error>)
        ensures
            res matches Ok(v) ==> {
                &&& Self::V::spec_apply(s@) is Ok
                &&& Self::V::spec_apply(s@) matches Ok(v_) && v@ == v_
            },
            res matches Err(e) ==> Self::V::spec_apply(s@) is Err,
    {
        assert(Self::V::spec_apply(s@) == <Self::Dst as View>::V::spec_try_from(s@))
            by (compute_only);
        Self::Dst::ex_try_from(s)
    }

    /// Applies the reverse faillible conversion to the destination type.
    fn rev_apply(s: Self::Dst) -> (res: Result<Self::Src, <Self::Src as TryFrom<Self::Dst>>::Error>)
        ensures
            res matches Ok(v) ==> {
                &&& Self::V::spec_rev_apply(s@) is Ok
                &&& Self::V::spec_rev_apply(s@) matches Ok(v_) && v@ == v_
            },
            res matches Err(e) ==> Self::V::spec_rev_apply(s@) is Err,
    {
        assert(Self::V::spec_rev_apply(s@) == <Self::Src as View>::V::spec_try_from(s@))
            by (compute_only);
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
    M: SpecTryFromInto<Src = Inner::SpecResult>,
    Inner::SpecResult: SpecTryFrom<M::Dst>,
    M::Dst: SpecTryFrom<Inner::SpecResult>,
 {
    type SpecResult = M::Dst;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match self.inner.spec_parse(s) {
            Err(e) => Err(e),
            Ok((n, v)) => match M::spec_apply(v) {
                Ok(v) => Ok((n, v)),
                Err(_) => Err(()),
            },
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.inner.spec_parse_wf(s);
        if let Ok((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        match M::spec_rev_apply(v) {
            Ok(v) => self.inner.spec_serialize(v),
            Err(_) => Err(()),
        }
    }
}

impl<Inner, M> SecureSpecCombinator for TryMap<Inner, M> where
    Inner: SecureSpecCombinator,
    M: SpecTryFromInto<Src = Inner::SpecResult>,
    Inner::SpecResult: SpecTryFrom<M::Dst>,
    M::Dst: SpecTryFrom<Inner::SpecResult>,
 {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(v_) = M::spec_rev_apply(v) {
            M::spec_iso_rev(v);
            self.inner.theorem_serialize_parse_roundtrip(v_);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.spec_parse_wf(buf);
        self.inner.theorem_parse_serialize_roundtrip(buf);
        if let Ok((n, v)) = self.inner.spec_parse(buf) {
            M::spec_iso(v)
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        if let Ok((n, v)) = self.inner.spec_parse(s1) {
            self.inner.spec_parse_wf(s1);
            M::spec_iso(v)
        }
    }
}

impl<I, O, Inner, M> Combinator<I, O> for TryMap<Inner, M> where
    I: VestSecretInput,
    O: VestSecretOutput<I>,
    Inner: Combinator<I, O>,
    Inner::V: SecureSpecCombinator<SpecResult = <Inner::Result as View>::V>,
    M: TryFromInto<Src = Inner::Result>,
    Inner::Result: TryFrom<M::Dst> + View,
    M::Dst: TryFrom<Inner::Result> + View,
    M::V: SpecTryFromInto<Src = <Inner::Result as View>::V, Dst = <M::Dst as View>::V>,
    <Inner::Result as View>::V: SpecTryFrom<<M::Dst as View>::V>,
    <M::Dst as View>::V: SpecTryFrom<<Inner::Result as View>::V>,
 {
    type Result = M::Dst;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Result), ParseError>) {
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

    fn serialize(&self, v: Self::Result, data: &mut O, pos: usize) -> (res: Result<
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

impl SpecTryFromInto for FieldLessMapper {
    type Src = FieldLessInner;
    type Dst = FieldLess;

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl TryFromInto for FieldLessMapper {
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
    <FieldLessCombinator as Combinator<&[u8], Vec<u8>>>::parse(&field_less(), i)
}

fn serialize_field_less(msg: FieldLess, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_field_less(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    <FieldLessCombinator as Combinator<&[u8], Vec<u8>>>::serialize(&field_less(), msg, data, pos)
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

} // verus!
