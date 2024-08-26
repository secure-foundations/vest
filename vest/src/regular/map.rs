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
    Self::V: SpecIso<Src = <Self::SrcOwned as View>::V, Dst = <Self::DstOwned as View>::V>,
    <Self::SrcOwned as View>::V: SpecFrom<<Self::DstOwned as View>::V>,
    <Self::DstOwned as View>::V: SpecFrom<<Self::SrcOwned as View>::V>,
 {
    /// The source type of the isomorphism.
    type Src<'a>: View<V = <Self::SrcOwned as View>::V> + From<Self::Dst<'a>>;

    /// The destination type of the isomorphism.
    type Dst<'a>: View<V = <Self::DstOwned as View>::V> + From<Self::Src<'a>>;

    /// The owned version of the source type.
    type SrcOwned: View + From<Self::DstOwned>;

    /// The owned version of the destination type.
    type DstOwned: View + From<Self::SrcOwned>;

    /// Applies the isomorphism to the source type.
    fn apply(s: Self::Src<'_>) -> (res: Self::Dst<'_>)
        ensures
            res@ == Self::V::spec_apply(s@),
    {
        assert(Self::V::spec_apply(s@) == <Self::Dst<'_> as View>::V::spec_from(s@))
            by (compute_only);
        Self::Dst::ex_from(s)
    }

    /// Applies the reverse isomorphism to the destination type.
    fn rev_apply(s: Self::Dst<'_>) -> (res: Self::Src<'_>)
        ensures
            res@ == Self::V::spec_rev_apply(s@),
    {
        assert(Self::V::spec_rev_apply(s@) == <Self::Src<'_> as View>::V::spec_from(s@))
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
    open spec fn spec_is_prefix_secure() -> bool {
        Inner::spec_is_prefix_secure()
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

impl<Inner, M> Combinator for Mapped<Inner, M> where
    Inner: Combinator,
    Inner::V: SecureSpecCombinator<SpecResult = <Inner::Owned as View>::V>,
    for <'a> M: Iso<Src<'a> = Inner::Result<'a>, SrcOwned = Inner::Owned>,
    for <'a>Inner::Result<'a>: From<M::Dst<'a>> + View,
    for <'a>M::Dst<'a>: From<Inner::Result<'a>> + View,
    M::V: SpecIso<Src = <Inner::Owned as View>::V, Dst = <M::DstOwned as View>::V>,
    <Inner::Owned as View>::V: SpecFrom<<M::DstOwned as View>::V>,
    <M::DstOwned as View>::V: SpecFrom<<Inner::Owned as View>::V>,
 {
    type Result<'a> = M::Dst<'a>;

    type Owned = M::DstOwned;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    fn exec_is_prefix_secure() -> (res: bool) {
        Inner::exec_is_prefix_secure()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        (),
    >) {
        self.inner.serialize(M::rev_apply(v), data, pos)
    }
}

} // verus!
