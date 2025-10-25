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
    type SpecResult = T::SpecResult;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.1.spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.1.spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.1.spec_serialize(v)
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for ImplicitTag<T> {
    open spec fn is_prefix_secure() -> bool {
        T::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.1.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.1.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.1.lemma_prefix_secure(s1, s2)
    }
}

impl<T: ASN1Tagged + Combinator> Combinator for ImplicitTag<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
{
    type Result<'a> = T::Result<'a>;
    type Owned = T::Owned;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        self.1.parse_requires()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.1.parse(s)
    }

    open spec fn serialize_requires(&self) -> bool {
        self.1.serialize_requires()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        self.1.serialize(v, data, pos)
    }
}

}
