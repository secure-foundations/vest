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
    type Type = PairValue<C1::Type, C2::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match (self.0, self.1).spec_parse(s) {
            Some((n, v)) => Some((n, PairValue(v.0, v.1))),
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (self.0, self.1).spec_serialize((v.0, v.1))
    }
}

impl<C1, C2> SecureSpecCombinator for Pair<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator,
{
    open spec fn is_prefix_secure() -> bool {
        C1::is_prefix_secure() && C2::is_prefix_secure()
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        (self.0, self.1).theorem_serialize_parse_roundtrip((v.0, v.1))
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (self.0, self.1).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        (self.0, self.1).lemma_prefix_secure(s1, s2)
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a, C1, C2> Combinator<'a, &'a [u8], Vec<u8>> for Pair<C1, C2> where
    C1: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    C2: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <C1 as View>::V: SecureSpecCombinator<Type = <<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View>::V>,
    <C2 as View>::V: SecureSpecCombinator<Type = <<C2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View>::V>,
{
    type Type = PairValue<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type, <C2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type>;
    type SType = PairValue<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType, <C2 as Combinator<'a, &'a [u8], Vec<u8>>>::SType>;

    fn length(&self, v: Self::SType) -> usize {
        self.0.length(v.0) + self.1.length(v.1)
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, v) = (&self.0, &self.1).parse(s)?;
        Ok((n, PairValue(v.0, v.1)))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        (&self.0, &self.1).serialize((v.0, v.1), data, pos)
    }
}

}
