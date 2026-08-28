//! Prototype: an unordered set of statically-known fields, encoded with existing combinators.
//!
//! This is the `N`-ary alternative to [`super::Permute3`]. Instead of enumerating the `N!` orderings
//! with nested `Alt`, it parses `N` elements of a single `Choice` tree and then constrains *which*
//! fields showed up:
//!
//! ```text
//! Elem = Choice<F1, Choice<F2, .. FN>>          // value is a nested Sum: it tags the field
//! SetN = Refined<Array<N, Elem>, presence_check>
//! ```
//!
//! [`Array<N, _>`](crate::combinators::Array) is the reason this is non-allocating: its executable
//! value is `[Elem::PT; N]`, a stack array, whereas `RepeatN` would produce a `Vec`.
//!
//! # Optional fields
//!
//! Optionality is controlled entirely by the presence check, once [`Empty`] is added as the last
//! branch of the `Choice` tree. `Empty` succeeds consuming zero bytes and `Choice` is left-biased,
//! so absent optional fields pad the array with zero-width elements and the arity stays fixed at
//! `N`. Note that a padding element can never precede a real field: `Empty` does not advance the
//! input, so once it is selected every later slot selects it too.
//!
//! # Why the check is phrased as tag distinctness
//!
//! With exactly `N` slots and `N` fields, "every field appears" and "no field appears twice" are
//! equivalent by pigeonhole, and the second is quantifier-free. That matters for proof automation:
//! the surjectivity phrasing (`forall k, exists i`) would put an existential in the `Refined`
//! predicate, which then appears in every `consistent` obligation downstream.
use crate::combinators::choice::Sum;
use crate::combinators::{Array, Choice, Const, Empty, Refined, U8};
use crate::core::exec::fns::Pred;
use crate::core::spec::SpecPred;
use vstd::prelude::*;

verus! {

// ============================================================================
// Variant A: three required fields
// ============================================================================

/// One element of a three-field set: whichever of the three fields matched.
pub type Elem3 = Choice<Const<U8, u8>, Choice<Const<U8, u8>, Const<U8, u8>>>;

/// The parsed value of [`Elem3`]; the `Sum` nesting records which field it was.
pub type Elem3Val = Sum<u8, Sum<u8, u8>>;

/// Field index (0, 1, or 2) that an element came from.
pub open spec fn tag3(e: Elem3Val) -> nat {
    match e {
        Sum::Inl(_) => 0nat,
        Sum::Inr(Sum::Inl(_)) => 1nat,
        Sum::Inr(Sum::Inr(_)) => 2nat,
    }
}

/// Executable counterpart of [`tag3`].
pub fn exec_tag3(e: &Elem3Val) -> (t: u8)
    ensures
        t as nat == tag3(e.deep_view()),
{
    match e {
        Sum::Inl(_) => 0,
        Sum::Inr(Sum::Inl(_)) => 1,
        Sum::Inr(Sum::Inr(_)) => 2,
    }
}

/// Presence check for three required fields: the three element tags are pairwise distinct, which
/// with three slots means each field occurs exactly once.
#[derive(Clone, Copy)]
pub struct AllThreePresent;

impl SpecPred<Seq<Elem3Val>> for AllThreePresent {
    open spec fn apply(&self, v: Seq<Elem3Val>) -> bool {
        &&& v.len() == 3
        &&& tag3(v[0]) != tag3(v[1])
        &&& tag3(v[0]) != tag3(v[2])
        &&& tag3(v[1]) != tag3(v[2])
    }
}

impl Pred<[Elem3Val; 3]> for AllThreePresent {
    fn test(&self, v: &[Elem3Val; 3]) -> (ok: bool) {
        let t0 = exec_tag3(&v[0]);
        let t1 = exec_tag3(&v[1]);
        let t2 = exec_tag3(&v[2]);
        t0 != t1 && t0 != t2 && t1 != t2
    }
}

/// An unordered set of exactly three required one-byte fields.
pub type Set3 = Refined<Array<3, Elem3>, AllThreePresent>;

/// Builds a [`Set3`] whose three fields are the constant bytes `f0`, `f1`, `f2`.
pub fn set3(f0: u8, f1: u8, f2: u8) -> (fmt: Set3)
    ensures
        fmt == Refined(
            Array::<3, Elem3>(Choice(Const(U8, f0), Choice(Const(U8, f1), Const(U8, f2)))),
            AllThreePresent,
        ),
{
    Refined(
        Array::<3, Elem3>(Choice(Const(U8, f0), Choice(Const(U8, f1), Const(U8, f2)))),
        AllThreePresent,
    )
}

// ============================================================================
// Variant B: first field required, last two optional
// ============================================================================

/// One element of a partially-optional three-field set. The trailing [`Empty`] branch is the
/// zero-width padding that stands in for an absent optional field.
pub type ElemOpt3 = Choice<Const<U8, u8>, Choice<Const<U8, u8>, Choice<Const<U8, u8>, Empty>>>;

/// The parsed value of [`ElemOpt3`].
pub type ElemOpt3Val = Sum<u8, Sum<u8, Sum<u8, ()>>>;

/// Tag for a padding element: not a field index.
pub const ABSENT_TAG: u8 = 3;

/// Field index (0, 1, or 2), or [`ABSENT_TAG`] for a padding element.
pub open spec fn tag_opt3(e: ElemOpt3Val) -> nat {
    match e {
        Sum::Inl(_) => 0nat,
        Sum::Inr(Sum::Inl(_)) => 1nat,
        Sum::Inr(Sum::Inr(Sum::Inl(_))) => 2nat,
        Sum::Inr(Sum::Inr(Sum::Inr(_))) => ABSENT_TAG as nat,
    }
}

/// Executable counterpart of [`tag_opt3`].
pub fn exec_tag_opt3(e: &ElemOpt3Val) -> (t: u8)
    ensures
        t as nat == tag_opt3(e.deep_view()),
{
    match e {
        Sum::Inl(_) => 0,
        Sum::Inr(Sum::Inl(_)) => 1,
        Sum::Inr(Sum::Inr(Sum::Inl(_))) => 2,
        Sum::Inr(Sum::Inr(Sum::Inr(_))) => ABSENT_TAG,
    }
}

/// Two element tags may coincide only if they are padding.
pub open spec fn no_repeated_field(x: nat, y: nat) -> bool {
    x == ABSENT_TAG as nat || y == ABSENT_TAG as nat || x != y
}

/// Presence check for one required field (index 0) and two optional ones: no field occurs twice,
/// and field 0 occurs.
#[derive(Clone, Copy)]
pub struct FirstRequired3;

impl SpecPred<Seq<ElemOpt3Val>> for FirstRequired3 {
    open spec fn apply(&self, v: Seq<ElemOpt3Val>) -> bool {
        &&& v.len() == 3
        &&& no_repeated_field(tag_opt3(v[0]), tag_opt3(v[1]))
        &&& no_repeated_field(tag_opt3(v[0]), tag_opt3(v[2]))
        &&& no_repeated_field(tag_opt3(v[1]), tag_opt3(v[2]))
        &&& (tag_opt3(v[0]) == 0nat || tag_opt3(v[1]) == 0nat || tag_opt3(v[2]) == 0nat)
    }
}

impl Pred<[ElemOpt3Val; 3]> for FirstRequired3 {
    fn test(&self, v: &[ElemOpt3Val; 3]) -> (ok: bool) {
        let t0 = exec_tag_opt3(&v[0]);
        let t1 = exec_tag_opt3(&v[1]);
        let t2 = exec_tag_opt3(&v[2]);
        let distinct = (t0 == ABSENT_TAG || t1 == ABSENT_TAG || t0 != t1) && (t0 == ABSENT_TAG || t2
            == ABSENT_TAG || t0 != t2) && (t1 == ABSENT_TAG || t2 == ABSENT_TAG || t1 != t2);
        distinct && (t0 == 0 || t1 == 0 || t2 == 0)
    }
}

/// An unordered set of three one-byte fields where only the first is required.
pub type SetOpt3 = Refined<Array<3, ElemOpt3>, FirstRequired3>;

/// Builds a [`SetOpt3`] whose fields are the constant bytes `f0` (required), `f1`, `f2`.
pub fn set_opt3(f0: u8, f1: u8, f2: u8) -> (fmt: SetOpt3)
    ensures
        fmt == Refined(
            Array::<3, ElemOpt3>(
                Choice(Const(U8, f0), Choice(Const(U8, f1), Choice(Const(U8, f2), Empty))),
            ),
            FirstRequired3,
        ),
{
    Refined(
        Array::<3, ElemOpt3>(
            Choice(Const(U8, f0), Choice(Const(U8, f1), Choice(Const(U8, f2), Empty))),
        ),
        FirstRequired3,
    )
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::exec::Parser;

    /// The `collect_into_declared_order` step, at the value level: this is what a forward-only
    /// `Mapped` layer would compute. Returns the fields in declared order.
    fn collect3(v: &[Elem3Val; 3]) -> (u8, u8, u8) {
        let mut out = (0u8, 0u8, 0u8);
        for e in v {
            match e {
                Sum::Inl(x) => out.0 = *x,
                Sum::Inr(Sum::Inl(x)) => out.1 = *x,
                Sum::Inr(Sum::Inr(x)) => out.2 = *x,
            }
        }
        out
    }

    fn collect_opt3(v: &[ElemOpt3Val; 3]) -> (u8, Option<u8>, Option<u8>) {
        let mut out = (0u8, None, None);
        for e in v {
            match e {
                Sum::Inl(x) => out.0 = *x,
                Sum::Inr(Sum::Inl(x)) => out.1 = Some(*x),
                Sum::Inr(Sum::Inr(Sum::Inl(x))) => out.2 = Some(*x),
                Sum::Inr(Sum::Inr(Sum::Inr(_))) => {}
            }
        }
        out
    }

    #[test]
    fn required_set_accepts_all_six_orders_and_projects_to_declared_order() {
        let fmt = set3(0xA1, 0xB2, 0xC3);

        for order in [
            [0xA1u8, 0xB2, 0xC3],
            [0xA1, 0xC3, 0xB2],
            [0xB2, 0xA1, 0xC3],
            [0xB2, 0xC3, 0xA1],
            [0xC3, 0xA1, 0xB2],
            [0xC3, 0xB2, 0xA1],
        ] {
            let (consumed, parsed) = fmt.parse(&&order[..]).expect(&format!("{order:02x?}"));
            assert_eq!(consumed, 3);
            // Whatever the arrival order, the projection is the declared order.
            assert_eq!(collect3(&parsed), (0xA1, 0xB2, 0xC3), "order {order:02x?}");
        }
    }

    #[test]
    fn required_set_rejects_duplicates_and_missing_fields() {
        let fmt = set3(0xA1, 0xB2, 0xC3);
        // Duplicate field: tags 0, 0, 1 -> not pairwise distinct.
        assert!(fmt.parse(&&[0xA1, 0xA1, 0xB2][..]).is_err());
        // Missing field 2: tags 0, 1, 1.
        assert!(fmt.parse(&&[0xA1, 0xB2, 0xB2][..]).is_err());
        // Too few elements for `Array<3>`.
        assert!(fmt.parse(&&[0xA1, 0xB2][..]).is_err());
        // An unknown byte cannot match any branch.
        assert!(fmt.parse(&&[0xA1, 0xB2, 0x99][..]).is_err());
    }

    #[test]
    fn optional_set_accepts_any_subset_containing_the_required_field() {
        let fmt = set_opt3(0xA1, 0xB2, 0xC3);

        // Required field only: two padding elements, one byte consumed.
        let (consumed, parsed) = fmt.parse(&&[0xA1][..]).unwrap();
        assert_eq!(consumed, 1);
        assert_eq!(collect_opt3(&parsed), (0xA1, None, None));

        // Each optional field on its own, in either order.
        for (bytes, expected) in [
            (vec![0xA1u8, 0xB2], (0xA1u8, Some(0xB2u8), None)),
            (vec![0xB2, 0xA1], (0xA1, Some(0xB2), None)),
            (vec![0xA1, 0xC3], (0xA1, None, Some(0xC3))),
            (vec![0xC3, 0xA1], (0xA1, None, Some(0xC3))),
        ] {
            let (consumed, parsed) = fmt.parse(&&bytes[..]).unwrap();
            assert_eq!(consumed, 2, "bytes {bytes:02x?}");
            assert_eq!(collect_opt3(&parsed), expected, "bytes {bytes:02x?}");
        }

        // All three present, in every order.
        for order in [
            [0xA1u8, 0xB2, 0xC3],
            [0xC3, 0xB2, 0xA1],
            [0xB2, 0xC3, 0xA1],
        ] {
            let (consumed, parsed) = fmt.parse(&&order[..]).unwrap();
            assert_eq!(consumed, 3);
            assert_eq!(collect_opt3(&parsed), (0xA1, Some(0xB2), Some(0xC3)));
        }
    }

    #[test]
    fn optional_set_rejects_missing_required_field_and_duplicates() {
        let fmt = set_opt3(0xA1, 0xB2, 0xC3);
        // Required field 0 absent.
        assert!(fmt.parse(&&[0xB2][..]).is_err());
        assert!(fmt.parse(&&[0xB2, 0xC3][..]).is_err());
        assert!(fmt.parse(&&[][..]).is_err());
        // Duplicate optional field.
        assert!(fmt.parse(&&[0xA1, 0xB2, 0xB2][..]).is_err());
        // Duplicate required field.
        assert!(fmt.parse(&&[0xA1, 0xA1][..]).is_err());
    }

    #[test]
    fn padding_elements_do_not_consume_input() {
        let fmt = set_opt3(0xA1, 0xB2, 0xC3);
        // Trailing bytes are left for the caller: only the fields are consumed.
        let (consumed, parsed) = fmt.parse(&&[0xA1, 0x99, 0x99][..]).unwrap();
        assert_eq!(consumed, 1);
        assert_eq!(collect_opt3(&parsed), (0xA1, None, None));
    }
}
