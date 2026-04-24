//! Executable fn traits.
use crate::combinators::mapped::spec::{SpecMap, SpecMapper};
use crate::core::exec::parser::*;
use crate::core::spec::{SafeParser, SpecParser, SpecPred};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

/// Executable counterpart of [`crate::core::spec::SpecPred`].
///
/// The executable method takes `&T` so callers can validate parsed values without moving them.
pub trait Pred<T: DeepView>: SpecPred<T::V> {
    fn test(&self, value: &T) -> (ok: bool)
        ensures
            ok == self.apply(value.deep_view()),
    ;
}

impl<T, P> Pred<T> for &P where T: DeepView, P: Pred<T> {
    fn test(&self, value: &T) -> (ok: bool) {
        (*self).test(value)
    }
}

/// Pairs an executable predicate closure with a ghost spec predicate.
pub struct FnPred<T: DeepView, Exec: Fn(&T) -> bool, Spec: SpecPred<T::V>> {
    exec_fn: Exec,
    spec_fn: Ghost<Spec>,
    marker: PhantomData<T>,
}

impl<T, Exec, Spec> FnPred<T, Exec, Spec> where
    T: DeepView,
    Exec: Fn(&T) -> bool,
    Spec: SpecPred<T::V>,
 {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& forall|v: &T| #[trigger] call_requires(self.exec_fn, (v,))
        &&& forall|v: &T, ok: bool| #[trigger]
            call_ensures(self.exec_fn, (v,), ok) ==> ok == {
                let Ghost(spec_pred) = self.spec_fn;
                spec_pred.apply(v.deep_view())
            }
    }

    pub fn new(exec_fn: Exec, Ghost(spec): Ghost<Spec>) -> (pred: Self)
        requires
            forall|v: &T| #[trigger] call_requires(exec_fn, (v,)),
            forall|v: &T, ok: bool| #[trigger]
                call_ensures(exec_fn, (v,), ok) ==> ok == spec.apply(v.deep_view()),
    {
        Self { exec_fn, spec_fn: Ghost(spec), marker: PhantomData }
    }
}

impl<T, Exec, Spec> SpecPred<T::V> for FnPred<T, Exec, Spec> where
    T: DeepView,
    Exec: Fn(&T) -> bool,
    Spec: SpecPred<T::V>,
 {
    closed spec fn apply(&self, value: T::V) -> bool {
        let Ghost(spec_pred) = self.spec_fn;
        spec_pred.apply(value)
    }
}

impl<T, Exec, Spec> Pred<T> for FnPred<T, Exec, Spec> where
    T: DeepView,
    Exec: Fn(&T) -> bool,
    Spec: SpecPred<T::V>,
 {
    fn test(&self, value: &T) -> (ok: bool) {
        proof {
            use_type_invariant(self);
        }
        (self.exec_fn)(value)
    }
}

pub trait Map: SpecMap {
    type I: DeepView<V = Self::SpecI>;

    type O: DeepView<V = Self::SpecO>;

    fn map(&self, i: Self::I) -> (o: Self::O)
        ensures
            self.spec_map(i.deep_view()) == o.deep_view(),
    ;
}

/// Pairs an executable predicate closure with a ghost spec predicate.
#[verifier::reject_recursive_types(O)]
pub struct FnMap<
    I: DeepView,
    O: DeepView,
    Exec: Fn(I) -> O,
    Spec: SpecMap<SpecI = I::V, SpecO = O::V>,
> {
    exec_fn: Exec,
    spec_fn: Ghost<Spec>,
    _marker: PhantomData<(I, O)>,
}

impl<I, O, Exec, Spec> FnMap<I, O, Exec, Spec> where
    I: DeepView,
    O: DeepView,
    Exec: Fn(I) -> O,
    Spec: SpecMap<SpecI = I::V, SpecO = O::V>,
 {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& forall|i: I| #[trigger] call_requires(self.exec_fn, (i,))
        &&& forall|i: I, o: O| #[trigger]
            call_ensures(self.exec_fn, (i,), o) ==> o.deep_view() == {
                let Ghost(spec_fn) = self.spec_fn;
                spec_fn.spec_map(i.deep_view())
            }
    }

    pub fn new(exec_fn: Exec, Ghost(spec): Ghost<Spec>) -> (pred: Self)
        requires
            forall|i: I| #[trigger] call_requires(exec_fn, (i,)),
            forall|i: I, o: O| #[trigger]
                call_ensures(exec_fn, (i,), o) ==> o.deep_view() == spec.spec_map(i.deep_view()),
    {
        Self { exec_fn, spec_fn: Ghost(spec), _marker: PhantomData }
    }
}

impl<I, O, Exec, Spec> SpecMap for FnMap<I, O, Exec, Spec> where
    I: DeepView,
    O: DeepView,
    Exec: Fn(I) -> O,
    Spec: SpecMap<SpecI = I::V, SpecO = O::V>,
 {
    type SpecI = I::V;

    type SpecO = O::V;

    closed spec fn spec_map(&self, i: Self::SpecI) -> Self::SpecO {
        let Ghost(spec_fn) = self.spec_fn;
        spec_fn.spec_map(i)
    }
}

impl<I, O, Exec, Spec> Map for FnMap<I, O, Exec, Spec> where
    I: DeepView,
    O: DeepView,
    Exec: Fn(I) -> O,
    Spec: SpecMap<SpecI = I::V, SpecO = O::V>,
 {
    type I = I;

    type O = O;

    fn map(&self, i: Self::I) -> (o: Self::O) {
        proof {
            use_type_invariant(self);
        }
        (self.exec_fn)(i)
    }
}

/// Pairs an executable parser closure with a ghost specification parser.
#[verifier::reject_recursive_types(O)]
pub struct FnParser<
    I: View<V = Seq<u8>>,
    O: DeepView,
    Spec: SpecParser<PVal = O::V>,
    Exec: Fn(&I) -> PResult<O>,
> {
    pub exec_fn: Exec,
    pub spec_fn: Ghost<Spec>,
    pub _marker: PhantomData<(I, O)>,
}

impl<I, O, Spec, Exec> FnParser<I, O, Spec, Exec> where
    I: View<V = Seq<u8>>,
    O: DeepView,
    Spec: SafeParser<PVal = O::V>,
    Exec: Fn(&I) -> PResult<O>,
 {
    pub fn new(exec_fn: Exec, Ghost(spec_fn): Ghost<Spec>) -> (parser: Self)
        requires
            spec_fn.safe_inv(),
            forall|i: &I| #[trigger] call_requires(exec_fn, (i,)),
            forall|i: &I, r: PResult<O>| #[trigger]
                call_ensures(exec_fn, (i,), r) ==> parse_matches_spec(r, spec_fn.spec_parse(i@)),
        ensures
            parser.exec_inv(),
            parser.safe_inv(),
            parser.spec_fn == spec_fn,
    {
        Self { exec_fn, spec_fn: Ghost(spec_fn), _marker: PhantomData }
    }
}

impl<I, O, Spec, Exec> SpecParser for FnParser<I, O, Spec, Exec> where
    I: View<V = Seq<u8>>,
    O: DeepView,
    Spec: SpecParser<PVal = O::V>,
    Exec: Fn(&I) -> PResult<O>,
 {
    type PVal = O::V;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let Ghost(spec_fn) = self.spec_fn;
        spec_fn.spec_parse(ibuf)
    }
}

impl<I, O, Spec, Exec> SafeParser for FnParser<I, O, Spec, Exec> where
    I: View<V = Seq<u8>>,
    O: DeepView,
    Spec: SafeParser<PVal = O::V>,
    Exec: Fn(&I) -> PResult<O>,
 {
    open spec fn safe_inv(&self) -> bool {
        let Ghost(spec_fn) = self.spec_fn;
        spec_fn.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let Ghost(spec_fn) = self.spec_fn;
        spec_fn.lemma_parse_safe(ibuf);
    }
}

impl<I, O, Spec, Exec> Parser<I> for FnParser<I, O, Spec, Exec> where
    I: View<V = Seq<u8>>,
    O: DeepView,
    Spec: SpecParser<PVal = O::V>,
    Exec: Fn(&I) -> PResult<O>,
 {
    type O = O;

    open spec fn exec_inv(&self) -> bool {
        &&& forall|i: &I| #[trigger] call_requires(self.exec_fn, (i,))
        &&& forall|i: &I, r: PResult<O>| #[trigger]
            call_ensures(self.exec_fn, (i,), r) ==> {
                let Ghost(spec_fn) = self.spec_fn;
                parse_matches_spec(r, spec_fn.spec_parse(i@))
            }
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<O>) {
        (self.exec_fn)(ibuf)
    }
}

} // verus!
