use super::*;
use vstd::prelude::*;

verus! {

/// SEQUENCE OF in ASN.1
#[derive(Debug, View)]
pub struct SequenceOf<C>(pub C);

pub type SequenceOfValue<T> = VecDeep<T>;

impl<C> ASN1Tagged for SequenceOf<C> {
    open spec fn spec_tag(&self) -> TagValue {
        tag_of!(SEQUENCE)
    }

    #[inline(always)]
    fn tag(&self) -> TagValue {
        tag_of!(SEQUENCE)
    }
}

impl<C: View> ViewWithASN1Tagged for SequenceOf<C> {
    proof fn lemma_view_preserves_tag(&self) {}
}

impl<C: SecureSpecCombinator + SpecCombinator> SpecCombinator for SequenceOf<C> {
    type SpecResult = Seq<C::SpecResult>;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_serialize(v)
    }
}

impl<C: SecureSpecCombinator + SpecCombinator> SecureSpecCombinator for SequenceOf<C> {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).lemma_prefix_secure(s1, s2);
    }
}

impl<C: Combinator> Combinator for SequenceOf<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    for<'a> C::Result<'a>: PolyfillClone,
{
    type Result<'a> = SequenceOfValue<C::Result<'a>>;
    type Owned = SequenceOfValue<C::Owned>;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        &&& <C as View>::V::is_prefix_secure()
        &&& self.0.parse_requires()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        ExplicitTag(self.tag(), Repeat(&self.0)).parse(s)
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& <C as View>::V::is_prefix_secure()
        &&& self.0.serialize_requires()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        ExplicitTag(self.tag(), Repeat(&self.0)).serialize(v, data, pos)
    }
}

}
