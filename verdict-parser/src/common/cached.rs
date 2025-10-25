use super::*;
use std::ops::Deref;
use vstd::prelude::*;

verus! {

/// Same behavior as T, but also returns the slice
/// consumed by T in the exec version
#[derive(View)]
pub struct Cached<T>(pub T);

pub struct CachedValue<'a, C: Combinator<'a>> where
    C::V: SecureSpecCombinator,
{
    inner: C::Result<'a>,
    combinator: Ghost<C>,
    serialized: &'a [u8],
}

/// View of CachedValue discards the serialization
impl<'a, C: Combinator<'a>> View for CachedValue<'a, C> where
    C::V: SecureSpecCombinator,
    for<'b> C::Result<'b>: View,
{
    type V = <C::Result<'a> as View>::V;

    closed spec fn view(&self) -> Self::V {
        self.inner@
    }
}

impl<'a, C: Combinator<'a>> PolyfillClone for CachedValue<'a, C> where
    C::V: SecureSpecCombinator,
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

impl<'a, C: Combinator<'a>> CachedValue<'a, C> where
    C::V: SecureSpecCombinator,
{
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.serialized@ =~= self.combinator@@.spec_serialize(self.inner@)
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
    type Type = T::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.0.spec_parse(s)
    }

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for Cached<T> {
    open spec fn is_prefix_secure() -> bool {
        T::is_prefix_secure()
    }
    
    spec fn is_productive() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a, T> Combinator<'a, &'a [u8], Vec<u8>> for Cached<T> where
    T: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator,
{
    type Type = CachedValue<'a, T>;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.0.length(v)
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    {
        let (n, x) = self.0.parse(s)?;
        proof {
            assert(s.len() <= usize::MAX);
            self@.theorem_parse_serialize_roundtrip(s@);
        }
        Ok((n, CachedValue { inner: x, combinator: Ghost(self.0), serialized: slice_take(s, n) }))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

}

impl<'a, C: Combinator<'a>> std::fmt::Debug for CachedValue<'a, C>
where
    C::V: SecureSpecCombinator,
    C::Result<'a>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

