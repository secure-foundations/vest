use vstd::prelude::*;

use crate::combinators::Either;

verus! {

/// The specification type (mathematical representation) of
/// a parsed/serialized value.
pub trait SpecType {
    open spec fn wf(&self) -> bool {
        true
    }

    spec fn byte_len(&self) -> nat;
}

impl SpecType for bool {
    open spec fn byte_len(&self) -> nat {
        1
    }
}

impl SpecType for u8 {
    open spec fn byte_len(&self) -> nat {
        1
    }
}

impl SpecType for u16 {
    open spec fn byte_len(&self) -> nat {
        2
    }
}

impl SpecType for u32 {
    open spec fn byte_len(&self) -> nat {
        4
    }
}

impl SpecType for u64 {
    open spec fn byte_len(&self) -> nat {
        8
    }
}

impl SpecType for usize {
    open spec fn byte_len(&self) -> nat {
        8
    }
}

impl SpecType for () {
    open spec fn byte_len(&self) -> nat {
        0
    }
}

impl<A: SpecType, B: SpecType> SpecType for (A, B) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf()
    }

    open spec fn byte_len(&self) -> nat {
        self.0.byte_len() + self.1.byte_len()
    }
}

impl<T: SpecType> SpecType for Option<T> {
    open spec fn wf(&self) -> bool {
        match self {
            Some(v) => v.wf(),
            None => true,
        }
    }

    open spec fn byte_len(&self) -> nat {
        match self {
            Some(v) => v.byte_len(),
            None => 0,
        }
    }
}

impl<A: SpecType, B: SpecType> SpecType for Either<A, B> {
    open spec fn wf(&self) -> bool {
        match self {
            Either::Left(v) => v.wf(),
            Either::Right(v) => v.wf(),
        }
    }

    open spec fn byte_len(&self) -> nat {
        match self {
            Either::Left(v) => v.byte_len(),
            Either::Right(v) => v.byte_len(),
        }
    }
}

impl<T: SpecType> SpecType for Seq<T> {
    open spec fn wf(&self) -> bool {
        forall|i: int| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }

    open spec fn byte_len(&self) -> nat {
        self.fold_left(0, |acc: nat, elem: T| acc + elem.byte_len())
    }
}

impl<const N: usize> SpecType for [u8; N] {
    open spec fn byte_len(&self) -> nat {
        N as nat
    }
}

/// Used as the associated type for `Refined` combinator.
pub struct Subset<T, Pred> {
    pub val: T,
    pub pred: Pred,
}

pub trait SpecPred<T> {
    spec fn apply(&self, value: T) -> bool;
}

pub type PredFnSpec<T> = spec_fn(T) -> bool;

impl<T> SpecPred<T> for PredFnSpec<T> {
    open spec fn apply(&self, value: T) -> bool {
        self(value)
    }
}

impl<T: SpecType, Pred: SpecPred<T>> SpecType for Subset<T, Pred> {
    open spec fn wf(&self) -> bool {
        &&& self.val.wf()
        &&& self.pred.apply(self.val)
    }

    open spec fn byte_len(&self) -> nat {
        self.val.byte_len()
    }
}

impl UniqueWfValue for () {
    proof fn lemma_unique_wf_value(&self, other: &Self) {
    }
}

/// A refinement of `SpecType` for types that have a unique well-formed value.
pub trait UniqueWfValue: SpecType {
    /// Lemma: if two values are both well-formed, they must be equal
    proof fn lemma_unique_wf_value(&self, other: &Self)
        ensures
            self.wf() && other.wf() ==> self == other,
    ;
}

pub trait NonEmptyValue: SpecType {
    open spec fn non_empty(&self) -> bool {
        true
    }

    /// Lemma: a well-formed value has a positive byte length
    proof fn lemma_non_empty(&self)
        requires
            self.non_empty(),
        ensures
            self.wf() ==> self.byte_len() > 0,
    ;
}

impl NonEmptyValue for bool {
    proof fn lemma_non_empty(&self) {
    }
}

impl NonEmptyValue for u8 {
    proof fn lemma_non_empty(&self) {
    }
}

impl NonEmptyValue for u16 {
    proof fn lemma_non_empty(&self) {
    }
}

impl NonEmptyValue for u32 {
    proof fn lemma_non_empty(&self) {
    }
}

impl NonEmptyValue for u64 {
    proof fn lemma_non_empty(&self) {
    }
}

impl NonEmptyValue for usize {
    proof fn lemma_non_empty(&self) {
    }
}

impl<A, B> NonEmptyValue for (A, B) where A: SpecType, B: SpecType {
    open spec fn non_empty(&self) -> bool {
        self.0.byte_len() > 0 || self.1.byte_len() > 0
    }

    proof fn lemma_non_empty(&self) {
    }
}

impl<A, B> NonEmptyValue for Either<A, B> where A: SpecType, B: SpecType {
    open spec fn non_empty(&self) -> bool {
        self.byte_len() > 0
    }

    proof fn lemma_non_empty(&self) {
    }
}

impl<T: NonEmptyValue> NonEmptyValue for Option<T> {
    open spec fn non_empty(&self) -> bool {
        self matches Some(v) && v.non_empty()
    }

    proof fn lemma_non_empty(&self) {
        self->0.lemma_non_empty();
    }
}

impl<T: NonEmptyValue> NonEmptyValue for Seq<T> {
    open spec fn non_empty(&self) -> bool {
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].non_empty()
        &&& self.len() > 0
    }

    proof fn lemma_non_empty(&self) {
        if self.wf() {
            let last_index = (self.len() as int) - 1;
            self[last_index].lemma_non_empty();
        }
    }
}

impl<const N: usize> NonEmptyValue for [u8; N] {
    open spec fn non_empty(&self) -> bool {
        N > 0
    }

    proof fn lemma_non_empty(&self) {
    }
}

impl<T: NonEmptyValue, Pred: SpecPred<T>> NonEmptyValue for Subset<T, Pred> {
    open spec fn non_empty(&self) -> bool {
        self.val.non_empty()
    }

    proof fn lemma_non_empty(&self) {
        self.val.lemma_non_empty();
    }
}

} // verus!
