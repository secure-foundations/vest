//! Executable predicate traits.
use crate::core::spec::SpecPred;
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

} // verus!
