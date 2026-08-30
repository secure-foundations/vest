//! Reusable executable and specification predicates for ASN.1 subtype constraints.
#[cfg(feature = "alloc")]
use super::{BmpString, Ia5StringOwned, PrintableStringOwned, TeletexStringOwned, Utf8StringOwned};
use super::{
    BmpStringSpec, Ia5String, Ia5StringSpec, Integer, PrintableString, PrintableStringSpec,
    TeletexString, TeletexStringSpec,
};
use crate::core::exec::fns::Pred;
use crate::core::spec::SpecPred;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// An ASN.1 `SIZE` interval.
///
/// Disabled bounds ignore their corresponding numeric const parameter. Keeping
/// both flags explicit mirrors ASN.1's `MIN` and `MAX` endpoints and avoids
/// approximating an unbounded specification with a machine maximum.
#[derive(Clone, Copy)]
pub struct Size<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize>;

/// An inclusive ASN.1 `INTEGER` value interval with independently optional bounds.
///
/// Bounds use `i64` because generated Rust values use the compact `Small` variant
/// in that range. Arbitrary-size `Big` values are also handled exactly: their
/// canonical representation proves that they lie strictly outside the `i64`
/// interval, so only their sign is needed at runtime.
#[derive(Clone, Copy)]
pub struct IntegerRange<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64>;

pub open spec fn integer_in_range<
    const HAS_MIN: bool,
    const MIN: i64,
    const HAS_MAX: bool,
    const MAX: i64,
>(value: int) -> bool {
    &&& (HAS_MIN ==> MIN as int <= value)
    &&& (HAS_MAX ==> value <= MAX as int)
}

fn integer_in_range_exec<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64>(
    value: i64,
) -> (ok: bool)
    ensures
        ok == integer_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value as int),
{
    (!HAS_MIN || MIN <= value) && (!HAS_MAX || value <= MAX)
}

impl<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64> SpecPred<
    int,
> for IntegerRange<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: int) -> bool {
        integer_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value)
    }
}

impl<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64> SpecPred<
    i8,
> for IntegerRange<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: i8) -> bool {
        integer_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value as int)
    }
}

impl<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64> Pred<
    i8,
> for IntegerRange<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &i8) -> (ok: bool) {
        integer_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(*value as i64)
    }
}

impl<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64> SpecPred<
    i16,
> for IntegerRange<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: i16) -> bool {
        integer_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value as int)
    }
}

impl<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64> Pred<
    i16,
> for IntegerRange<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &i16) -> (ok: bool) {
        integer_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(*value as i64)
    }
}

impl<'a, const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64> Pred<
    Integer<'a>,
> for IntegerRange<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &Integer<'a>) -> (ok: bool) {
        value.in_i64_range::<HAS_MIN, MIN, HAS_MAX, MAX>()
    }
}

pub open spec fn size_in_range<
    const HAS_MIN: bool,
    const MIN: usize,
    const HAS_MAX: bool,
    const MAX: usize,
>(len: nat) -> bool {
    &&& (HAS_MIN ==> MIN as nat <= len)
    &&& (HAS_MAX ==> len <= MAX as nat)
}

fn size_in_range_exec<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize>(
    len: usize,
) -> (ok: bool)
    ensures
        ok == size_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(len as nat),
{
    (!HAS_MIN || MIN <= len) && (!HAS_MAX || len <= MAX)
}

impl<T, const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> SpecPred<
    Seq<T>,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: Seq<T>) -> bool {
        size_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value.len())
    }
}

impl<
    'a,
    T: DeepView,
    const HAS_MIN: bool,
    const MIN: usize,
    const HAS_MAX: bool,
    const MAX: usize,
> Pred<&'a [T]> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &&'a [T]) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.len())
    }
}

#[cfg(feature = "alloc")]
impl<
    T: DeepView,
    const HAS_MIN: bool,
    const MIN: usize,
    const HAS_MAX: bool,
    const MAX: usize,
> Pred<Vec<T>> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &Vec<T>) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.len())
    }
}

impl<'a, const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    &'a str,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &&'a str) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.unicode_len())
    }
}

#[cfg(feature = "alloc")]
impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    Utf8StringOwned,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &Utf8StringOwned) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.as_str().unicode_len())
    }
}

impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> SpecPred<
    PrintableStringSpec,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: PrintableStringSpec) -> bool {
        size_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner.len())
    }
}

impl<'a, const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    PrintableString<'a>,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &PrintableString<'a>) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

#[cfg(feature = "alloc")]
impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    PrintableStringOwned,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &PrintableStringOwned) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> SpecPred<
    Ia5StringSpec,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: Ia5StringSpec) -> bool {
        size_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner.len())
    }
}

impl<'a, const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    Ia5String<'a>,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &Ia5String<'a>) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

#[cfg(feature = "alloc")]
impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    Ia5StringOwned,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &Ia5StringOwned) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> SpecPred<
    TeletexStringSpec,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: TeletexStringSpec) -> bool {
        size_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner.len())
    }
}

impl<'a, const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    TeletexString<'a>,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &TeletexString<'a>) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

#[cfg(feature = "alloc")]
impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    TeletexStringOwned,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &TeletexStringOwned) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> SpecPred<
    BmpStringSpec,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    open spec fn apply(&self, value: BmpStringSpec) -> bool {
        size_in_range::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner.len())
    }
}

#[cfg(feature = "alloc")]
impl<const HAS_MIN: bool, const MIN: usize, const HAS_MAX: bool, const MAX: usize> Pred<
    BmpString,
> for Size<HAS_MIN, MIN, HAS_MAX, MAX> {
    fn test(&self, value: &BmpString) -> (ok: bool) {
        size_in_range_exec::<HAS_MIN, MIN, HAS_MAX, MAX>(value.inner().unicode_len())
    }
}

/// Logical union of two executable/specification predicates.
#[derive(Copy)]
pub struct ConstraintOr<L, R>(pub L, pub R);

impl<L: Clone, R: Clone> Clone for ConstraintOr<L, R> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(L::clone, (&self.0,), cloned.0),
            call_ensures(R::clone, (&self.1,), cloned.1),
    {
        ConstraintOr(self.0.clone(), self.1.clone())
    }
}

impl<T, L: SpecPred<T>, R: SpecPred<T>> SpecPred<T> for ConstraintOr<L, R> {
    open spec fn apply(&self, value: T) -> bool {
        self.0.apply(value) || self.1.apply(value)
    }
}

impl<T: DeepView, L: Pred<T>, R: Pred<T>> Pred<T> for ConstraintOr<L, R> {
    fn test(&self, value: &T) -> (ok: bool) {
        self.0.test(value) || self.1.test(value)
    }
}

/// Logical intersection of two executable/specification predicates.
#[derive(Copy)]
pub struct ConstraintAnd<L, R>(pub L, pub R);

impl<L: Clone, R: Clone> Clone for ConstraintAnd<L, R> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(L::clone, (&self.0,), cloned.0),
            call_ensures(R::clone, (&self.1,), cloned.1),
    {
        ConstraintAnd(self.0.clone(), self.1.clone())
    }
}

impl<T, L: SpecPred<T>, R: SpecPred<T>> SpecPred<T> for ConstraintAnd<L, R> {
    open spec fn apply(&self, value: T) -> bool {
        self.0.apply(value) && self.1.apply(value)
    }
}

impl<T: DeepView, L: Pred<T>, R: Pred<T>> Pred<T> for ConstraintAnd<L, R> {
    fn test(&self, value: &T) -> (ok: bool) {
        self.0.test(value) && self.1.test(value)
    }
}

/// Logical complement of an executable/specification predicate.
#[derive(Copy)]
pub struct ConstraintNot<P>(pub P);

impl<P: Clone> Clone for ConstraintNot<P> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(P::clone, (&self.0,), cloned.0),
    {
        ConstraintNot(self.0.clone())
    }
}

impl<T, P: SpecPred<T>> SpecPred<T> for ConstraintNot<P> {
    open spec fn apply(&self, value: T) -> bool {
        !self.0.apply(value)
    }
}

impl<T: DeepView, P: Pred<T>> Pred<T> for ConstraintNot<P> {
    fn test(&self, value: &T) -> (ok: bool) {
        !self.0.test(value)
    }
}

} // verus!
