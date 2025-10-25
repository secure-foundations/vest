use super::*;
/// Use a custom pair type so that we can impl traits on it
use vstd::prelude::*;

verus! {

#[derive(Debug, View)]
pub struct Pair<C1, C2>(pub C1, pub C2);

#[derive(Debug, View, PolyfillClone)]
pub struct PairValue<T1, T2>(pub T1, pub T2);

impl<C1, C2> SpecCombinator for Pair<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator,
{
    type SpecResult = PairValue<C1::SpecResult, C2::SpecResult>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match (self.0, self.1).spec_parse(s) {
            Ok((n, v)) => Ok((n, PairValue(v.0, v.1))),
            Err(()) => Err(()),
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        (self.0, self.1).spec_serialize((v.0, v.1))
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        (self.0, self.1).spec_parse_wf(s)
    }
}

impl<C1, C2> SecureSpecCombinator for Pair<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator,
{
    open spec fn is_prefix_secure() -> bool {
        C1::is_prefix_secure() && C2::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        (self.0, self.1).theorem_serialize_parse_roundtrip((v.0, v.1))
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (self.0, self.1).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        (self.0, self.1).lemma_prefix_secure(s1, s2)
    }
}

impl<C1, C2> Combinator for Pair<C1, C2> where
    C1: Combinator,
    C2: Combinator,
    C1::V: SecureSpecCombinator<SpecResult = <C1::Owned as View>::V>,
    C2::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V>,
{
    type Result<'a> = PairValue<C1::Result<'a>, C2::Result<'a>>;
    type Owned = PairValue<C1::Owned, C2::Owned>;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(0)
    }

    fn length(&self) -> Option<usize> {
        Some(0)
    }

    open spec fn parse_requires(&self) -> bool {
        &&& self.0.parse_requires()
        &&& self.1.parse_requires()
        &&& C1::V::is_prefix_secure()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (n, v) = (&self.0, &self.1).parse(s)?;
        Ok((n, PairValue(v.0, v.1)))
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.0.serialize_requires()
        &&& self.1.serialize_requires()
        &&& C1::V::is_prefix_secure()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        (&self.0, &self.1).serialize((v.0, v.1), data, pos)
    }
}

}
