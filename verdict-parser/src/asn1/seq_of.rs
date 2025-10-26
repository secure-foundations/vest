use super::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

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

impl<'a, C> Combinator<'a, &'a [u8], Vec<u8>> for SequenceOf<C> where
    C: SpecCombinator
        + SecureSpecCombinator
        + ViewWithASN1Tagged
        + for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <C as View>::V: SecureSpecCombinator<Type = <C as SpecCombinator>::Type>,
    <C as View>::V: ASN1Tagged,
    for<'x> <C as Combinator<'x, &'x [u8], Vec<u8>>>::Type: View<V = <C as SpecCombinator>::Type> + PolyfillClone,
    <C as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <C as SpecCombinator>::Type> + PolyfillClone,
{
    type Type = SequenceOfValue<<C as Combinator<'a, &'a [u8], Vec<u8>>>::Type>;
    type SType = SequenceOfValue<<C as Combinator<'a, &'a [u8], Vec<u8>>>::SType>;

    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::external_body]
    fn length(&self, v: Self::SType) -> usize {
        let mut inner_len: usize = 0;
        let mut idx = 0;
        while idx < v.len() {
            let elem_len = self.0.length(v.get(idx).clone());
            match inner_len.checked_add(elem_len) {
                Some(total) => inner_len = total,
                None => return usize::MAX,
            }
            idx += 1;
        }

        let tag_len = ASN1Tag.length(self.tag());
        let len_len = Length.length(inner_len as LengthValue);
        if let Some(total) = tag_len.checked_add(len_len) {
            if let Some(final_total) = total.checked_add(inner_len) {
                final_total
            } else {
                usize::MAX
            }
        } else {
            usize::MAX
        }
    }

    #[inline(always)]
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::external_body]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        proof {
            self.0.lemma_view_preserves_tag();
        }

        let expected_tag = self.tag();
        let (tag_len, tag) = ASN1Tag.parse(s)?;
        if !tag.eq(expected_tag) {
            return Err(ParseError::Other("Unmatching tags".to_string()));
        }

        let after_tag = slice_subrange(s, tag_len, s.len());
        let (len_len, length_value) = Length.parse(after_tag)?;
        let header_len = tag_len + len_len;

        if length_value > s.len() - header_len {
            return Err(ParseError::UnexpectedEndOfInput);
        }

        let payload_end = header_len + length_value;
        let payload = slice_subrange(s, header_len, payload_end);

        let mut items: SequenceOfValue<<C as Combinator<'a, &'a [u8], Vec<u8>>>::Type> = SequenceOfValue::new();
        let mut offset: usize = 0;

        while offset < length_value {
            let (consumed, value) = self.0.parse(slice_subrange(payload, offset, payload.len()))?;
            if consumed == 0 || consumed > length_value - offset {
                return Err(ParseError::Other("Invalid element in SEQUENCE OF".to_string()));
            }
            items.push(value);
            offset += consumed;
        }

        if offset != length_value {
            return Err(ParseError::Other("Sequence payload length mismatch".to_string()));
        }

        Ok((payload_end, items))
    }

    #[inline(always)]
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::external_body]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        proof {
            self.0.lemma_view_preserves_tag();
        }

        let mut inner_len: usize = 0;
        let mut idx = 0;
        while idx < v.len() {
            let elem_len = self.0.length(v.get(idx).clone());
            match inner_len.checked_add(elem_len) {
                Some(total) => inner_len = total,
                None => return Err(SerializeError::Other("Size overflow".to_string())),
            }
            idx += 1;
        }

        let tag_len = ASN1Tag.serialize(self.tag(), data, pos)?;
        let len_len = Length.serialize(inner_len as LengthValue, data, pos + tag_len)?;

        let mut written: usize = 0;
        for elem in v.into_iter() {
            let consumed = self.0.serialize(elem, data, pos + tag_len + len_len + written)?;
            match written.checked_add(consumed) {
                Some(total) => written = total,
                None => return Err(SerializeError::Other("Size overflow".to_string())),
            }
        }

        if written != inner_len {
            return Err(SerializeError::Other("Sequence payload length mismatch".to_string()));
        }

        Ok(tag_len + len_len + written)
    }
}

}
