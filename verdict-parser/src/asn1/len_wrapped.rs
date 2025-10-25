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

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match new_spec_length_wrapped_inner(self.0).spec_parse(s) {
            Some((len, (_, v))) => Some((len, v)),
            None => None,
        }
    }

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        let buf = self.0.spec_serialize(v);
        new_spec_length_wrapped_inner(self.0).spec_serialize((buf.len() as LengthValue, v))
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for LengthWrapped<T> {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    spec fn is_productive() -> bool {
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
    T: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: PolyfillClone,
{
    type Type = <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    fn length(&self, v: Self::SType) -> usize {
        let inner_len = self.0.length(v);
        Length.length(inner_len as LengthValue) + inner_len
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (len, (_, v)) = new_length_wrapped_inner(&self.0).parse(s)?;
        Ok((len, v))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        // TODO: can we avoid serializing twice?
        let len = self.0.serialize(v.clone(), data, pos)?;
        let final_len = new_length_wrapped_inner(&self.0).serialize((len as LengthValue, v), data, pos)?;

        if pos < data.len() && final_len < data.len() - pos {
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
            return Ok(final_len);
        }

        Err(SerializeError::InsufficientBuffer)
    }
}

/// The function |i| AndThen<Bytes, T>
pub struct LengthWrappedCont<'a, T>(pub &'a T);

impl<'b, T: Combinator<'b>> Continuation<POrSType<&LengthValue, LengthValue>> for LengthWrappedCont<'b, T> where
    <T as View>::V: SecureSpecCombinator,
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
closed spec fn new_spec_length_wrapped_inner<T: SpecCombinator>(inner: T) -> SpecLengthWrappedInner<T> {
    Pair::spec_new(Length, |l| AndThen(bytes::Variable(l as usize), inner))
}

#[inline(always)]
fn new_length_wrapped_inner<'a, T: Combinator<'a>>(inner: &'a T) -> (res: LengthWrappedInner<'a, T>) where
    <T as View>::V: SecureSpecCombinator,
    ensures
        res@ == new_spec_length_wrapped_inner(inner@),
{
    Pair::new(Length, LengthWrappedCont(inner))
}

}
