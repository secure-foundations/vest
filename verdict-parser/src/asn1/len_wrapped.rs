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
    type SpecResult = T::SpecResult;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_length_wrapped_inner(self.0).spec_parse(s) {
            Ok((len, (_, v))) => Ok((len, v)),
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_length_wrapped_inner(self.0).spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        match self.0.spec_serialize(v) {
            // Need to compute the inner serialized length first
            Ok(buf) => new_spec_length_wrapped_inner(self.0).spec_serialize((buf.len() as LengthValue, v)),
            Err(..) => Err(()),
        }
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for LengthWrapped<T> {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(buf) = self.0.spec_serialize(v) {
            new_spec_length_wrapped_inner(self.0).theorem_serialize_parse_roundtrip((buf.len() as LengthValue, v))
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_length_wrapped_inner(self.0).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_length_wrapped_inner(self.0).lemma_prefix_secure(s1, s2)
    }
}

impl<T: Combinator> Combinator for LengthWrapped<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    for<'a> T::Result<'a>: PolyfillClone,
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
        self.0.parse_requires()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, (_, v)) = new_length_wrapped_inner(&self.0).parse(s)?;
        Ok((len, v))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
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

impl<'b, T: Combinator> Continuation for LengthWrappedCont<'b, T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
{
    type Input<'a> = LengthValue;
    type Output = AndThen<Bytes, &'b T>;

    #[inline(always)]
    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        AndThen(Bytes(i as usize), &self.0)
    }

    closed spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    closed spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        &&& self.0.parse_requires() ==> o.parse_requires()
        &&& self.0.serialize_requires() ==> o.serialize_requires()
        &&& o@ == AndThen(Bytes(i as usize), self.0@)
    }
}

#[allow(dead_code)]
type SpecLengthWrappedInner<T> = SpecDepend<Length, AndThen<Bytes, T>>;
type LengthWrappedInner<'a, T> = Depend<Length, AndThen<Bytes, &'a T>, LengthWrappedCont<'a, T>>;

/// SpecDepend version of new_length_wrapped_inner
closed spec fn new_spec_length_wrapped_inner<T: SpecCombinator>(inner: T) -> SpecLengthWrappedInner<T> {
    SpecDepend {
        fst: Length,
        snd: |l| {
            AndThen(Bytes(l as usize), inner)
        },
    }
}

/// Spec version of new_length_wrapped_inner
closed spec fn new_length_wrapped_inner_spec<'a, T: Combinator>(inner: &'a T) -> LengthWrappedInner<'a, T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
{
    Depend {
        fst: Length,
        snd: LengthWrappedCont(inner),
        spec_snd: Ghost(|l| {
            AndThen(Bytes(l as usize), inner@)
        }),
    }
}

#[inline(always)]
fn new_length_wrapped_inner<'a, T: Combinator>(inner: &'a T) -> (res: LengthWrappedInner<'a, T>) where
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,

    ensures
        res == new_length_wrapped_inner_spec(inner),
        res@ == new_spec_length_wrapped_inner(inner@),
{
    Depend {
        fst: Length,
        snd: LengthWrappedCont(inner),
        spec_snd: Ghost(|l| {
            AndThen(Bytes(l as usize), inner@)
        }),
    }
}

}
