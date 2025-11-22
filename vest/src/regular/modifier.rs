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
pub trait Iso<'x>: View where
    Self::V: SpecIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecFrom<<Self::Src as View>::V>,
    Self::Dst: 'x,
 {
    /// The source type of the isomorphism.
    type Src: View;

    /// The reference of the [`Src`] type.
    type RefSrc: View<V = <Self::Src as View>::V> + From<&'x Self::Dst>;

    /// The destination type of the isomorphism.
    type Dst: View + From<Self::Src>;
}

/// The bijective functions of [`Iso`]
/// [`Self::apply`] and [`Self::rev_apply`] must be inverses of each other.
/// See [`SpecIsoFn::spec_iso`] and [`SpecIsoFn::spec_iso_rev`] for more details.
pub trait IsoFn<'x>: Iso<'x> where
    Self::V: SpecIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecFrom<<Self::Src as View>::V>,
    Self::Dst: 'x,
 {
    /// Applies the isomorphism to the source type.
    fn apply(s: Self::Src) -> (res: Self::Dst)
        ensures
            res@ == Self::V::spec_apply(s@),
    ;

    /// Applies the reverse isomorphism to the destination type.
    fn rev_apply(s: &'x Self::Dst) -> (res: Self::RefSrc)
        ensures
            res@ == Self::V::spec_rev_apply(s@),
    ;
}

// Blanket implementation for all types that implement `Iso`
impl<'x, T: Iso<'x>> IsoFn<'x> for T where
    T::V: SpecIso<Src = <T::Src as View>::V, Dst = <T::Dst as View>::V>,
    <T::Src as View>::V: SpecFrom<<T::Dst as View>::V>,
    <T::Dst as View>::V: SpecFrom<<T::Src as View>::V>,
    Self::Dst: 'x,
 {
    fn apply(s: Self::Src) -> (res: Self::Dst) {
        Self::Dst::ex_from(s)
    }

    fn rev_apply(s: &'x Self::Dst) -> (res: Self::RefSrc) {
        Self::RefSrc::ex_from(s)
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

    open spec fn requires(&self) -> bool {
        self.inner.requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(M::spec_rev_apply(v))
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.inner.spec_parse(s) {
            Some((n, v)) => Some((n, M::spec_apply(v))),
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
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
        let buf = self.inner.spec_serialize(M::spec_rev_apply(v));
        M::spec_iso_rev(v);
        self.inner.theorem_serialize_parse_roundtrip(M::spec_rev_apply(v))
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.lemma_parse_length(buf);
        self.inner.theorem_parse_serialize_roundtrip(buf);
        if let Some((n, v)) = self.inner.spec_parse(buf) {
            M::spec_iso(v)
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        if let Some((n, v)) = self.inner.spec_parse(s1) {
            self.inner.lemma_parse_length(s1);
            M::spec_iso(v)
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.inner.lemma_parse_length(s);
        if let Some((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.inner.lemma_parse_productive(s);
        if let Some((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }
}

impl<'x, I, O, Inner, M> Combinator<'x, I, O> for Mapped<Inner, M> where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O>,
    Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V>,
    M: Iso<'x, Src = Inner::Type, RefSrc = Inner::SType>,
    M::Dst: From<Inner::Type> + View,
    Inner::SType: From<&'x M::Dst> + View,
    M::V: SpecIsoProof<Src = <Inner::Type as View>::V, Dst = <M::Dst as View>::V>,
    <Inner::Type as View>::V: SpecFrom<<M::Dst as View>::V>,
    <M::Dst as View>::V: SpecFrom<<Inner::Type as View>::V>,
 {
    type Type = M::Dst;

    type SType = &'x M::Dst;

    fn length(&self, v: Self::SType) -> usize {
        self.inner.length(M::rev_apply(v))
    }

    open spec fn ex_requires(&self) -> bool {
        self.inner.ex_requires()
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

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
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

/// The fallible functions of [`SpecPartialIso`]
pub trait SpecPartialIsoFn: SpecPartialIso {
    /// Applies the fallible conversion to the source type.
    spec fn spec_apply(s: Self::Src) -> Result<
        Self::Dst,
        <Self::Dst as SpecTryFrom<Self::Src>>::Error,
    >;

    /// Applies the reverse fallible conversion to the destination type.
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
            Self::spec_apply(s) matches Ok(d) ==> Self::spec_rev_apply(d) == Ok::<
                _,
                <Self::Src as SpecTryFrom<Self::Dst>>::Error,
            >(s),
    ;

    /// The other direction of the isomorphism when the conversion is successful.
    proof fn spec_iso_rev(d: Self::Dst)
        ensures
            Self::spec_rev_apply(d) matches Ok(s) ==> Self::spec_apply(s) == Ok::<
                _,
                <Self::Dst as SpecTryFrom<Self::Src>>::Error,
            >(d),
    ;
}

/// Fallible version of [`Iso`].
pub trait PartialIso<'x>: View where
    Self::V: SpecPartialIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecTryFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecTryFrom<<Self::Src as View>::V>,
    Self::Dst: 'x,
 {
    /// The source type
    type Src: View;

    /// The reference of the [`Src`] type.
    type RefSrc: View<V = <Self::Src as View>::V> + TryFrom<&'x Self::Dst>;

    /// The destination type
    type Dst: View + TryFrom<Self::Src>;
}

/// The fallible functions of [`PartialIso`]
pub trait PartialIsoFn<'x>: PartialIso<'x> where
    Self::V: SpecPartialIso<Src = <Self::Src as View>::V, Dst = <Self::Dst as View>::V>,
    <Self::Src as View>::V: SpecTryFrom<<Self::Dst as View>::V>,
    <Self::Dst as View>::V: SpecTryFrom<<Self::Src as View>::V>,
    Self::Dst: 'x,
 {
    /// Applies the fallible conversion to the source type.
    fn apply(s: Self::Src) -> (res: Result<Self::Dst, <Self::Dst as TryFrom<Self::Src>>::Error>)
        ensures
            res matches Ok(v) ==> {
                &&& Self::V::spec_apply(s@) is Ok
                &&& Self::V::spec_apply(s@) matches Ok(v_) && v@ == v_
            },
            res matches Err(e) ==> Self::V::spec_apply(s@) is Err,
    ;

    /// Applies the reverse fallible conversion to the destination type.
    fn rev_apply(s: &'x Self::Dst) -> (res: Result<
        Self::RefSrc,
        <Self::RefSrc as TryFrom<&'x Self::Dst>>::Error,
    >)
        ensures
            res matches Ok(v) ==> {
                &&& Self::V::spec_rev_apply(s@) is Ok
                &&& Self::V::spec_rev_apply(s@) matches Ok(v_) && v@ == v_
            },
            res matches Err(e) ==> Self::V::spec_rev_apply(s@) is Err,
    ;
}

// Blanket implementation for all types that implement `PartialIso`
impl<'x, T: PartialIso<'x>> PartialIsoFn<'x> for T where
    T::V: SpecPartialIso<Src = <T::Src as View>::V, Dst = <T::Dst as View>::V>,
    <T::Src as View>::V: SpecTryFrom<<T::Dst as View>::V>,
    <T::Dst as View>::V: SpecTryFrom<<T::Src as View>::V>,
    Self::Dst: 'x,
 {
    fn apply(s: Self::Src) -> (res: Result<Self::Dst, <Self::Dst as TryFrom<Self::Src>>::Error>) {
        Self::Dst::ex_try_from(s)
    }

    fn rev_apply(s: &'x Self::Dst) -> (res: Result<
        Self::RefSrc,
        <Self::RefSrc as TryFrom<&'x Self::Dst>>::Error,
    >) {
        Self::RefSrc::ex_try_from(s)
    }
}

/// Combinator that maps the result of an `inner` combinator with a fallible conversion
/// that implements [`TryFromInto`].
pub struct TryMap<Inner, M> {
    /// The inner combinator.
    pub inner: Inner,
    /// The fallible conversion.
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

    open spec fn requires(&self) -> bool {
        self.inner.requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        match M::spec_rev_apply(v) {
            Ok(v) => self.inner.wf(v),
            Err(_) => false,
        }
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.inner.spec_parse(s) {
            Some((n, v)) => match M::spec_apply(v) {
                Ok(v) => Some((n, v)),
                Err(_) => None,
            },
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        match M::spec_rev_apply(v) {
            Ok(v) => self.inner.spec_serialize(v),
            Err(_) => Seq::empty(),  // won't happen when `self.wf(v)`
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
        if let Some((n, v)) = self.inner.spec_parse(buf) {
            M::spec_iso(v)
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        if let Some((n, v)) = self.inner.spec_parse(s1) {
            self.inner.lemma_parse_length(s1);
            M::spec_iso(v)
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.inner.lemma_parse_length(s);
        if let Some((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.inner.lemma_parse_productive(s);
        if let Some((n, v)) = self.inner.spec_parse(s) {
            M::spec_iso(v);
        }
    }
}

impl<'x, I, O, Inner, M> Combinator<'x, I, O> for TryMap<Inner, M> where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O>,
    Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V>,
    M: PartialIso<'x, Src = Inner::Type, RefSrc = Inner::SType>,
    M::Dst: TryFrom<Inner::Type> + View,
    Inner::SType: TryFrom<&'x M::Dst> + View,
    M::V: SpecPartialIsoProof<Src = <Inner::Type as View>::V, Dst = <M::Dst as View>::V>,
    <Inner::Type as View>::V: SpecTryFrom<<M::Dst as View>::V>,
    <M::Dst as View>::V: SpecTryFrom<<Inner::Type as View>::V>,
    <Inner::SType as TryFrom<&'x M::Dst>>::Error: core::fmt::Debug,
 {
    type Type = M::Dst;

    type SType = &'x M::Dst;

    fn length(&self, v: Self::SType) -> usize {
        self.inner.length(M::rev_apply(v).unwrap())
    }

    open spec fn ex_requires(&self) -> bool {
        self.inner.ex_requires()
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

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        // we know `v` is well-formed, so we can unwrap it
        self.inner.serialize(M::rev_apply(v).unwrap(), data, pos)
    }
}

/// The spec version of [`Pred`].
pub trait SpecPred<Input> {
    // /// The input type of the predicate.
    // type Input;
    /// Applies the predicate to the input.
    spec fn spec_apply(&self, i: &Input) -> bool;
}

/// All predicates to be used in [`Refined`] combinator must implement this trait.
pub trait Pred<Input: View + ?Sized>: View where Self::V: SpecPred<<Input as View>::V> {
    // /// The input type of the predicate.
    // type Input: View + ?Sized;
    /// Applies the predicate to the input.
    fn apply(&self, i: &Input) -> (res: bool)
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
    P: SpecPred<Inner::Type>,
 {
    type Type = Inner::Type;

    open spec fn requires(&self) -> bool {
        self.inner.requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.inner.wf(v) && self.predicate.spec_apply(&v)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.inner.spec_parse(s) {
            Some((n, v)) if self.predicate.spec_apply(&v) => Some((n, v)),
            _ => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<Inner, P> SecureSpecCombinator for Refined<Inner, P> where
    Inner: SecureSpecCombinator,
    P: SpecPred<Inner::Type>,
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
        assert(Self::is_prefix_secure() ==> self.spec_parse(s1) is Some ==> self.spec_parse(
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

impl<'x, I, O, Inner, P> Combinator<'x, I, O> for Refined<Inner, P> where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O, SType = &'x <Inner as Combinator<'x, I, O>>::Type>,
    Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V>,
    P: Pred<Inner::Type>,
    P::V: SpecPred<<Inner::Type as View>::V>,
    Inner::Type: 'x,
 {
    type Type = Inner::Type;

    type SType = Inner::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.inner.length(v)
    }

    open spec fn ex_requires(&self) -> bool {
        self.inner.ex_requires()
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

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        // we know `v` is well-formed, so we can skip the predicate check
        self.inner.serialize(v, data, pos)
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

    open spec fn requires(&self) -> bool {
        self.inner.requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        &&& self.inner.wf(v)
        // call `serializer` only if `cond` is true
        &&& self.cond
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if self.cond {
            self.inner.spec_parse(s)
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<Inner: SecureSpecCombinator> SecureSpecCombinator for Cond<Inner> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.inner.theorem_serialize_parse_roundtrip(v);
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

impl<'x, I: VestInput, O: VestOutput<I>, Inner: Combinator<'x, I, O>> Combinator<'x, I, O> for Cond<
    Inner,
> where Inner::V: SecureSpecCombinator<Type = <Inner::Type as View>::V> {
    type Type = Inner::Type;

    type SType = Inner::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.inner.length(v)
    }

    open spec fn ex_requires(&self) -> bool {
        self.inner.ex_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if self.cond {
            self.inner.parse(s)
        } else {
            Err(ParseError::CondFailed)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        // we know `self.cond` must be true when `serialize` is called
        // so we can skip the check
        self.inner.serialize(v, data, pos)
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

    open spec fn requires(&self) -> bool {
        self.0.requires() && self.1.requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.1.wf(v) && self.0.wf(self.1.spec_serialize(v))
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, v1)) = self.0.spec_parse(s) {
            if let Some((m, v2)) = self.1.spec_parse(v1) {
                // !! for security, can only proceed if the `Next` parser consumed the entire
                // !! output from the `Prev` parser
                if m == n {
                    Some((n, v2))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        let buf1 = self.1.spec_serialize(v);
        self.0.spec_serialize(buf1)
    }
}

impl<Next: SecureSpecCombinator> SecureSpecCombinator for AndThen<Variable, Next> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let buf1 = self.1.spec_serialize(v);
        self.1.theorem_serialize_parse_roundtrip(v);
        self.0.theorem_serialize_parse_roundtrip(buf1);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, v1)) = self.0.spec_parse(buf) {
            if let Some((m, v2)) = self.1.spec_parse(v1) {
                self.0.theorem_parse_serialize_roundtrip(buf);
                self.1.theorem_parse_serialize_roundtrip(v1);
                if m == n {
                    let buf2 = self.1.spec_serialize(v2);
                    let buf1 = self.0.spec_serialize(buf2);
                    assert(buf1 == buf.subrange(0, n as int));
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
        if let Some((n, v1)) = self.0.spec_parse(s) {
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

impl<'x, I, O, Next: Combinator<'x, I, O>> Combinator<'x, I, O> for AndThen<Variable, Next> where
    I: VestInput,
    O: VestOutput<I>,
    Next::V: SecureSpecCombinator<Type = <Next::Type as View>::V>,
 {
    type Type = Next::Type;

    type SType = Next::SType;

    fn length(&self, _v: Self::SType) -> usize {
        self.0.0
    }

    open spec fn ex_requires(&self) -> bool {
        self.1.ex_requires()
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

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        // we can skip the call to `self.0.serialize` because we know that it
        // will be an "no-op"
        let n = self.1.serialize(v, data, pos)?;
        Ok(n)
    }
}

} // verus!
