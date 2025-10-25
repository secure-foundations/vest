use super::*;
use vstd::prelude::*;

verus! {

/// Implicit tagging replaces the tag value in the ASN1Tagged trait,
/// but otherwise parses/serializes exactly the same way as the inner combinator
#[derive(Debug, View)]
pub struct ImplicitTag<T>(pub TagValue, pub T);

impl<T> ASN1Tagged for ImplicitTag<T> {
    open spec fn spec_tag(&self) -> TagValue {
        self.0
    }

    #[inline(always)]
    fn tag(&self) -> TagValue {
        self.0.clone()
    }
}

impl<T: View> ViewWithASN1Tagged for ImplicitTag<T> {
    proof fn lemma_view_preserves_tag(&self) {}
}

impl<T: SpecCombinator> SpecCombinator for ImplicitTag<T> {
    type Type = T::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.1.spec_parse(s)
    }

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.1.spec_serialize(v)
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for ImplicitTag<T> {
    open spec fn is_prefix_secure() -> bool {
        T::is_prefix_secure()
    }
    
    spec fn is_productive() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.1.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.1.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.1.lemma_prefix_secure(s1, s2)
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a, T> Combinator<'a, &'a [u8], Vec<u8>> for ImplicitTag<T> where
    T: ASN1Tagged + for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator + ASN1Tagged,
{
    type Type = <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.1.length(v)
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        self.1.parse(s)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        self.1.serialize(v, data, pos)
    }
}

}
