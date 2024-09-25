use crate::properties::*;
use vstd::prelude::*;

verus! {

/// The spec version of [`Pred`].
pub trait SpecPred {
    /// The input type of the predicate.
    type Input;

    /// Applies the predicate to the input.
    spec fn spec_apply(&self, i: &Self::Input) -> bool;
}

/// All predicates to be used in [`Refined`] combinator must implement this trait.
pub trait Pred: View where Self::V: SpecPred<Input = <Self::InputOwned as View>::V> {
    /// The input type of the predicate.
    type Input<'a>: View<V = <Self::InputOwned as View>::V>;

    /// The owned version of the input type.
    type InputOwned: View;

    /// Applies the predicate to the input.
    fn apply(&self, i: &Self::Input<'_>) -> (res: bool)
        ensures
            res == self@.spec_apply(&i@),
    ;
}

/// Combinator that refines the result of an `inner` combinator with a predicate that implements
/// [`Pred`].
pub struct Refined<Inner, P> {
    /// The inner combinator.
    pub inner: Inner,
    /// The predicate.
    pub predicate: P,
}

impl<Inner: View, P: View> View for Refined<Inner, P> where  {
    type V = Refined<Inner::V, P::V>;

    open spec fn view(&self) -> Self::V {
        Refined { inner: self.inner@, predicate: self.predicate@ }
    }
}

impl<Inner, P> SpecCombinator for Refined<Inner, P> where
    Inner: SpecCombinator,
    P: SpecPred<Input = Inner::SpecResult>,
 {
    type SpecResult = Inner::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match self.inner.spec_parse(s) {
            Ok((n, v)) if self.predicate.spec_apply(&v) => Ok((n, v)),
            _ => Err(()),
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if self.predicate.spec_apply(&v) {
            self.inner.spec_serialize(v)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.inner.spec_parse_wf(s);
    }
}

impl<Inner, P> SecureSpecCombinator for Refined<Inner, P> where
    Inner: SecureSpecCombinator,
    P: SpecPred<Input = Inner::SpecResult>,
 {
    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.inner.theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.inner.lemma_prefix_secure(s1, s2);
        assert(Self::is_prefix_secure() ==> self.spec_parse(s1).is_ok() ==> self.spec_parse(
            s1.add(s2),
        ) == self.spec_parse(s1));
    }
}

impl<Inner, P> Combinator for Refined<
    Inner,
    P,
> where
    Inner: Combinator,
    Inner::V: SecureSpecCombinator<SpecResult = <Inner::Owned as View>::V>,
    P: for <'a>Pred<Input<'a> = Inner::Result<'a>, InputOwned = Inner::Owned>,
    P::V: SpecPred<Input = <Inner::Owned as View>::V>,
 {
    type Result<'a> = Inner::Result<'a>;

    type Owned = Inner::Owned;

    open spec fn spec_length(&self) -> Option<usize> {
        self.inner.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.inner.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> Result<(usize, Self::Result<'a>), ParseError> {
        match self.inner.parse(s) {
            Ok((n, v)) => if self.predicate.apply(&v) {
                Ok((n, v))
            } else {
                Err(ParseError::RefinedPredicateFailed)
            },
            Err(e) => Err(e),
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        if self.predicate.apply(&v) {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::RefinedPredicateFailed)
        }
    }
}

} // verus!
