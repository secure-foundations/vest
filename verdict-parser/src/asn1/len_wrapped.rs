use super::*;
use vstd::prelude::*;

verus! {

/// Wrap the inner combinator in a Length-Buffer pair
#[derive(Debug)]
pub struct LengthWrapped<T>(pub T);

impl<T: View> View for LengthWrapped<T> {
    type V = LengthWrapped<T::V>;

    open spec fn view(&self) -> Self::V {
        LengthWrapped(self.0@)
    }
}

impl<T: SpecCombinator> SpecCombinator for LengthWrapped<T> {
    type Type = T::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match new_spec_length_wrapped_inner(self.0).spec_parse(s) {
            Some((len, (_, v))) => Some((len, v)),
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        let buf = self.0.spec_serialize(v);
        new_spec_length_wrapped_inner(self.0).spec_serialize((buf.len() as LengthValue, v))
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for LengthWrapped<T> {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let buf = self.0.spec_serialize(v);
        new_spec_length_wrapped_inner(self.0).theorem_serialize_parse_roundtrip((buf.len() as LengthValue, v))
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_length_wrapped_inner(self.0).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_length_wrapped_inner(self.0).lemma_prefix_secure(s1, s2)
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a, T> Combinator<'a, &'a [u8], Vec<u8>> for LengthWrapped<T> where
    T: SpecCombinator
        + SecureSpecCombinator
        + for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    for<'x> <T as Combinator<'x, &'x [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
{
    type Type = <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    #[verifier::external_body]
    fn length(&self, v: Self::SType) -> usize {
        let inner_len = self.0.length(v);
        Length.length(inner_len as LengthValue) + inner_len
    }

    #[inline(always)]
    #[verifier::external_body]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (len_len, length_value) = Length.parse(s)?;
        let payload_len = length_value as usize;

        if len_len > s.len() {
            return Err(ParseError::UnexpectedEndOfInput);
        }

        if payload_len > s.len() - len_len {
            return Err(ParseError::UnexpectedEndOfInput);
        }

        if len_len > usize::MAX - payload_len {
            return Err(ParseError::Other("Length overflow".to_string()));
        }

        let payload_end = len_len + payload_len;
        let payload = slice_subrange(s, len_len, payload_end);
        let (consumed, value) = self.0.parse(payload)?;

        if consumed != payload_len {
            return Err(ParseError::Other("Length mismatch".to_string()));
        }

        Ok((payload_end, value))
    }

    #[inline(always)]
    #[verifier::external_body]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let inner_len = self.0.length(v.clone());
        let len_len = Length.serialize(inner_len as LengthValue, data, pos)?;

        if len_len > usize::MAX - inner_len {
            return Err(SerializeError::Other("Length overflow".to_string()));
        }

        if pos > usize::MAX - len_len {
            return Err(SerializeError::InsufficientBuffer);
        }

        let consumed = self.0.serialize(v, data, pos + len_len)?;
        if consumed != inner_len {
            return Err(SerializeError::Other("Length mismatch".to_string()));
        }

        Ok(len_len + consumed)
    }
}

/// The function |i| AndThen<Bytes, T>
pub struct LengthWrappedCont<'a, T>(pub &'a T);

impl<'a, T> View for LengthWrappedCont<'a, T> where
    T: SpecCombinator
        + SecureSpecCombinator
        + Combinator<'a, &'a [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
{
    type V = spec_fn(LengthValue) -> AndThen<bytes::Variable, <T as View>::V>;

    open spec fn view(&self) -> Self::V {
        new_spec_length_wrapped_inner(self.0@).snd
    }
}

impl<'b, T> Continuation<POrSType<&LengthValue, LengthValue>> for LengthWrappedCont<'b, T> where
    T: SpecCombinator
        + SecureSpecCombinator
        + Combinator<'b, &'b [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'b, &'b [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
    <T as Combinator<'b, &'b [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
{
    type Output = AndThen<bytes::Variable, &'b T>;

    open spec fn requires(&self, i: POrSType<&LengthValue, LengthValue>) -> bool {
        true
    }

    open spec fn ensures(&self, deps: POrSType<&LengthValue, LengthValue>, o: Self::Output) -> bool {
        let i = match deps {
            POrSType::P(i) => *i,
            POrSType::S(i) => i,
        };
        &&& o@ == AndThen(bytes::Variable(i as usize), self.0@)
    }

    fn apply(&self, deps: POrSType<&LengthValue, LengthValue>) -> (o: Self::Output) {
        let i = match deps {
            POrSType::P(i) => *i,
            POrSType::S(i) => i,
        };
        AndThen(bytes::Variable(i as usize), &self.0)
    }
}

#[allow(dead_code)]
type SpecLengthWrappedInner<T> = SpecDepend<Length, AndThen<bytes::Variable, T>>;
type LengthWrappedInner<'a, T> = Depend<Length, AndThen<bytes::Variable, &'a T>, LengthWrappedCont<'a, T>>;

/// SpecDepend version of new_length_wrapped_inner
pub closed spec fn new_spec_length_wrapped_inner<T: SpecCombinator>(inner: T) -> SpecLengthWrappedInner<T> {
    Pair::spec_new(Length, |l| AndThen(bytes::Variable(l as usize), inner))
}

#[inline(always)]
fn new_length_wrapped_inner<'a, T>(inner: &'a T) -> (res: LengthWrappedInner<'a, T>) where
    T: SpecCombinator
        + SecureSpecCombinator
        + Combinator<'a, &'a [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type> + PolyfillClone,
    ensures
        res@ == new_spec_length_wrapped_inner(inner@),
{
    Pair::new(Length, LengthWrappedCont(inner))
}

}
