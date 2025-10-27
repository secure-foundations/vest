use super::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// SEQUENCE OF in ASN.1
#[derive(Debug, View)]
pub struct SequenceOf<C>(pub C);

pub type SequenceOfValue<T> = RepeatResult<T>;

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
    type Type = Seq<C::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).wf(v)
    }
    
    open spec fn requires(&self) -> bool {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_serialize(v)
    }
}

impl<C: SecureSpecCombinator + SpecCombinator> SecureSpecCombinator for SequenceOf<C> {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).lemma_prefix_secure(s1, s2);
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

// impl<I, O, C, 'x> Combinator<'x, I, O> for Repeat<C> where
//     I: VestInput,
//     O: VestOutput<I>,
//     C: Combinator<'x, I, O, SType = &'x <C as Combinator<'x, I, O>>::Type>,
//     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
//     <C as Combinator<'x, I, O>>::Type: 'x,
//  {
//     type Type = RepeatResult<C::Type>;

//     type SType = &'x RepeatResult<C::Type>;

impl<'a, C> Combinator<'a, &'a [u8], Vec<u8>> for SequenceOf<C> where
    C: SecureSpecCombinator
        + ViewWithASN1Tagged
        + Combinator<'a, &'a [u8], Vec<u8>, SType = &'a <C as Combinator<'a, &'a [u8], Vec<u8>>>::Type>,
    <C as Combinator<'a, &'a [u8], Vec<u8>>>::Type: 'a,
    <C as View>::V: SecureSpecCombinator<Type = <C as SpecCombinator>::Type>,
    <C as View>::V: ASN1Tagged,
    <C as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <C as SpecCombinator>::Type>,
    <C as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <C as SpecCombinator>::Type>,
{
    type Type = SequenceOfValue<<C as Combinator<'a, &'a [u8], Vec<u8>>>::Type>;
    type SType = &'a SequenceOfValue<<C as Combinator<'a, &'a [u8], Vec<u8>>>::Type>;

    open spec fn ex_requires(&self) -> bool {
        ExplicitTag(tag_of!(SEQUENCE), Repeat(&self.0)).ex_requires()
    }

    fn length(&self, v: Self::SType) -> usize {
        ExplicitTag(self.tag(), Repeat(&self.0)).length(&v)
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        ExplicitTag(self.tag(), Repeat(&self.0)).parse(s)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        ExplicitTag(self.tag(), Repeat(&self.0)).serialize(v, data, pos)
    }
}

}
