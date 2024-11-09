use crate::properties::*;
use vstd::prelude::*;

verus! {

/// The spec version of [`Pred`].
pub trait SpecPred<'a> {
    /// The input type of the predicate.
    type Input;

    /// Applies the predicate to the input.
    spec fn spec_apply(&self, i: &Self::Input) -> bool;
}

/// All predicates to be used in [`Refined`] combinator must implement this trait.
pub trait Pred: View where Self::V: for<'a> SpecPred<'a, Input = <Self::Input<'a> as View>::V> {
    /// The input type of the predicate.
    type Input<'a>: View;

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

impl<'a, Inner, P> SpecCombinator<'a> for Refined<Inner, P> where
    Inner: SpecCombinator<'a>,
    P: SpecPred<'a, Input = Inner::SpecResult>,
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

impl<'a, Inner, P> SecureSpecCombinator<'a> for Refined<Inner, P> where
    Inner: SecureSpecCombinator<'a>,
    P: SpecPred<'a, Input = Inner::SpecResult>,
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

impl<Inner, P> Combinator for Refined<Inner, P> where
    Inner: Combinator,
    Inner::V: for <'spec>SecureSpecCombinator<'spec, SpecResult = <Inner::Result<'spec> as View>::V>,
    P: for <'a>Pred<Input<'a> = Inner::Result<'a>>,
    P::V: for<'spec>SpecPred<'spec, Input = <Inner::Result<'spec> as View>::V>,
 {
    type Result<'a> = Inner::Result<'a>;

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

// Alternative implementation of `Refined` that uses the `Continuation` trait.
// #[verifier::reject_recursive_types(InnerResult)]
// pub struct SpecRefined<Inner, InnerResult> {
//     pub inner: Inner,
//     pub pred: spec_fn(InnerResult) -> bool,
// }
//
// impl<'a, Inner, InnerResult> SpecCombinator<'a> for SpecRefined<Inner, InnerResult> where
//     Inner: SpecCombinator<'a, SpecResult = InnerResult>,
//  {
//     type SpecResult = Inner::SpecResult;
//
//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
//         match self.inner.spec_parse(s) {
//             Ok((n, v)) if (self.pred)(v) => Ok((n, v)),
//             _ => Err(()),
//         }
//     }
//
//     open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
//         if (self.pred)(v) {
//             self.inner.spec_serialize(v)
//         } else {
//             Err(())
//         }
//     }
//
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//         self.inner.spec_parse_wf(s);
//     }
// }
//
// impl<'a, Inner, InnerResult> SecureSpecCombinator<'a> for SpecRefined<Inner, InnerResult> where
//     Inner: SecureSpecCombinator<'a, SpecResult = InnerResult>,
//  {
//     open spec fn is_prefix_secure() -> bool {
//         Inner::is_prefix_secure()
//     }
//
//     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
//         self.inner.theorem_serialize_parse_roundtrip(v);
//     }
//
//     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
//         self.inner.theorem_parse_serialize_roundtrip(buf);
//     }
//
//     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
//         self.inner.lemma_prefix_secure(s1, s2);
//     }
// }
//
// /// Combinator that refines the result of an `inner` combinator with a predicate that implements
// /// [`Pred`].
// pub struct Refined<Inner, InnerResult: View, Pred> {
//     /// The inner combinator.
//     pub inner: Inner,
//     /// The predicate.
//     pub pred: Pred,
//     /// The spec version of the predicate.
//     pub spec_pred: Ghost<spec_fn(InnerResult::V) -> bool>,
// }
//
// impl<Inner, InnerResult, Pred> Refined<Inner, InnerResult, Pred> where
//     InnerResult: View,
//     Pred: for <'r>Continuation<&'r InnerResult, Output = bool>,
//  {
//     /// well-formed [`Refined`] should have its predicate [`pred`] well-formed w.r.t. [`spec_pred`]
//     pub open spec fn wf(&self) -> bool {
//         let Ghost(spec_pred) = self.spec_pred;
//         &&& forall|i| #[trigger] self.pred.requires(i)
//         &&& forall|i, o| self.pred.ensures(i, o) ==> spec_pred(i@) == o@
//     }
// }
//
// impl<Inner: View, InnerResult: View, Pred> View for Refined<Inner, InnerResult, Pred> {
//     type V = SpecRefined<Inner::V, InnerResult::V>;
//
//     open spec fn view(&self) -> Self::V {
//         let Ghost(spec_pred) = self.spec_pred;
//         SpecRefined { inner: self.inner@, pred: spec_pred }
//     }
// }
//
// impl<Inner, InnerResult, Pred> Combinator for Refined<
//     Inner,
//     InnerResult,
//     Pred,
// > where
//     Inner: for<'a>Combinator<Result<'a> = InnerResult>,
//     Inner::V: for <'spec>SecureSpecCombinator<
//         'spec,
//         SpecResult = <Inner::Result<'spec> as View>::V,
//     >,
//     Pred: for <'r>Continuation<&'r InnerResult, Output = bool>,
//     InnerResult: View,
//  {
//     type Result<'a> = Inner::Result<'a>;
//
//     open spec fn spec_length(&self) -> Option<usize> {
//         self.inner.spec_length()
//     }
//
//     fn length(&self) -> Option<usize> {
//         self.inner.length()
//     }
//
//     open spec fn parse_requires(&self) -> bool {
//         &&& self.wf()
//         &&& self.inner.parse_requires()
//     }
//
//     fn parse<'a>(&self, s: &'a [u8]) -> Result<(usize, Self::Result<'a>), ParseError> {
//         match self.inner.parse(s) {
//             Ok((n, v)) => if self.pred.apply(&v) {
//                 Ok((n, v))
//             } else {
//                 Err(ParseError::RefinedPredicateFailed)
//             },
//             Err(e) => Err(e),
//         }
//     }
//
//     open spec fn serialize_requires(&self) -> bool {
//         &&& self.wf()
//         &&& self.inner.serialize_requires()
//     }
//
//     fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<
//         usize,
//         SerializeError,
//     > {
//         if self.pred.apply(&v) {
//             self.inner.serialize(v, data, pos)
//         } else {
//             Err(SerializeError::RefinedPredicateFailed)
//         }
//     }
// }

} // verus!
