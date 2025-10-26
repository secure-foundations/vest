use super::*;
use vstd::prelude::*;

verus! {

/// Explicit tagging wrapps the inner combinator in a new TLV tuple
/// Equivalent to ImplicitTag(tag, LengthWrapped(inner))
#[derive(Debug, View)]
pub struct ExplicitTag<T>(pub TagValue, pub T);

impl<T> ASN1Tagged for ExplicitTag<T> {
    open spec fn spec_tag(&self) -> TagValue {
        self.0
    }

    #[inline(always)]
    fn tag(&self) -> TagValue {
        self.0.clone()
    }
}

impl<T: View> ViewWithASN1Tagged for ExplicitTag<T> {
    proof fn lemma_view_preserves_tag(&self) {}
}

impl<T: SpecCombinator> SpecCombinator for ExplicitTag<T> {
    type Type = T::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.1.wf(v)
    }
    
    open spec fn requires(&self) -> bool {
        self.1.requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        LengthWrapped(self.1).spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        LengthWrapped(self.1).spec_serialize(v)
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for ExplicitTag<T> {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        LengthWrapped(self.1).theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        LengthWrapped(self.1).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        LengthWrapped(self.1).lemma_prefix_secure(s1, s2)
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a, T> Combinator<'a, &'a [u8], Vec<u8>> for ExplicitTag<T> where
    T: SpecCombinator
        + SecureSpecCombinator
        + for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    for<'x> <T as Combinator<'x, &'x [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
{
    type Type = <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    fn length(&self, v: Self::SType) -> usize {
        LengthWrapped(&self.1).length(v)
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        LengthWrapped(&self.1).parse(s)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        LengthWrapped(&self.1).serialize(v, data, pos)
    }
}

}
