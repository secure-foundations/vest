use super::*;
use std::ops::Deref;
use vstd::prelude::*;

verus! {

/// Same behavior as T, but also returns the slice
/// consumed by T in the exec version
#[derive(View)]
pub struct Cached<T>(pub T);

pub struct CachedValue<'a, C: Combinator> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    inner: C::Result<'a>,
    combinator: Ghost<C>,
    serialized: &'a [u8],
}

/// View of CachedValue discards the serialization
impl<'a, C: Combinator> View for CachedValue<'a, C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    for<'b> C::Result<'b>: View,
{
    type V = <C::Result<'a> as View>::V;

    closed spec fn view(&self) -> Self::V {
        self.inner@
    }
}

impl<'a, C: Combinator> PolyfillClone for CachedValue<'a, C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    C::Result<'a>: PolyfillClone,
{
    #[inline(always)]
    fn clone(&self) -> Self {
        proof {
            use_type_invariant(self);
        }
        CachedValue {
            inner: self.inner.clone(),
            combinator: self.combinator,
            serialized: self.serialized,
        }
    }
}

impl<'a, C: Combinator> CachedValue<'a, C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        let res = self.combinator@@.spec_serialize(self.inner@);
        &&& res.is_ok()
        &&& self.serialized@ =~= res.unwrap()
    }

    #[inline(always)]
    pub fn get(&self) -> (res: &C::Result<'a>)
        ensures res@ == self@
    {
        &self.inner
    }

    /// Since we can't expose any of self's fields, we can't check if
    /// the combinator expected by the user is the same as self.combinator
    ///
    /// But the type of self.combinator is exposed to the user, and
    /// if there is a unique constructor for that type, then we can
    /// deduce that the serialized result would be the same.
    #[inline(always)]
    pub fn serialize(&self) -> (res: &[u8])
        requires forall |c1: C, c2: C| c1.view() == c2.view()
        ensures forall |c: C| (#[trigger] c.view()).spec_serialize(self@) matches Ok(r) && r == res@
    {
        proof {
            use_type_invariant(self);
        }
        self.serialized
    }
}

impl<T: SpecCombinator> SpecCombinator for Cached<T> {
    type SpecResult = T::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for Cached<T> {
    open spec fn is_prefix_secure() -> bool {
        T::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(s)
    }
}

impl<T: Combinator> Combinator for Cached<T> where
    T::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
{
    type Result<'a> = CachedValue<'a, T>;
    type Owned = T::Owned;

    open spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>)
    {
        let (n, x) = self.0.parse(s)?;
        proof {
            assert(s.len() <= usize::MAX);
            self@.theorem_parse_serialize_roundtrip(s@);
        }
        Ok((n, CachedValue { inner: x, combinator: Ghost(self.0), serialized: slice_take(s, n) }))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v.inner, data, pos)
    }
}

}

impl<'a, C: Combinator> std::fmt::Debug for CachedValue<'a, C>
where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    C::Result<'a>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}
