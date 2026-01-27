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
        &&& self.0.wf(v)
        &&& new_spec_length_wrapped_inner(self.0).wf((self.0.spec_serialize(v).len() as LengthValue, v)) 
    }
    
    open spec fn requires(&self) -> bool {
        &&& self.0.requires()
        &&& new_spec_length_wrapped_inner(self.0).requires()
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
        + Combinator<'a, &'a [u8], Vec<u8>, SType = &'a <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type> + 'a,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type>,
{
    type Type = <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType;

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires()
    }

    fn length(&self, v: Self::SType) -> usize {
        let len = self.0.length(v);
        let inner = new_length_wrapped_inner(&self.0);
        let final_len = inner.length((len as LengthValue, v));
        final_len
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (len, (_, v)) = new_length_wrapped_inner(&self.0).parse(s)?;
        Ok((len, v))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let len = self.0.length(v);
        let final_len = new_length_wrapped_inner(&self.0).serialize((len as LengthValue, v), data, pos)?;

        if pos < data.len() && final_len < data.len() - pos {
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@)));
            return Ok(final_len);
        }

        Err(SerializeError::InsufficientBuffer)
    }
}

/// The function |i| AndThen<Bytes, T>
pub struct LengthWrappedCont<'a, T>(pub &'a T);

impl<'a, 'b, T> View for LengthWrappedCont<'b, T> where
    T: SecureSpecCombinator + Combinator<'a, &'a [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type>,
{
    type V = spec_fn(LengthValue) -> AndThen<bytes::Variable, <T as View>::V>;

    open spec fn view(&self) -> Self::V {
        new_spec_length_wrapped_inner(self.0@).snd
    }
}

impl<'a, 'b, T> Continuation<POrSType<&LengthValue, LengthValue>> for LengthWrappedCont<'b, T> where
    T: SpecCombinator
        + SecureSpecCombinator
        + Combinator<'a, &'a [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type>,
{
    type Output = AndThen<bytes::Variable, &'b T>;

    open spec fn requires(&self, i: POrSType<&LengthValue, LengthValue>) -> bool {
        self.0.ex_requires()
    }

    open spec fn ensures(&self, deps: POrSType<&LengthValue, LengthValue>, o: Self::Output) -> bool {
        &&& o.ex_requires()
        &&& o@ == (new_spec_length_wrapped_inner(self.0@).snd)(deps@)
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
fn new_length_wrapped_inner<'a, 'b, T>(inner: &'b T) -> (res: LengthWrappedInner<'b, T>) where
    T: SecureSpecCombinator + Combinator<'a, &'a [u8], Vec<u8>>,
    <T as View>::V: SecureSpecCombinator<Type = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::Type: View<V = <T as SpecCombinator>::Type>,
    <T as Combinator<'a, &'a [u8], Vec<u8>>>::SType: View<V = <T as SpecCombinator>::Type>,
    ensures
        res.snd == LengthWrappedCont(inner),
        res@ == new_spec_length_wrapped_inner(inner@),
{
    Pair::new(Length, LengthWrappedCont(inner))
}

}
