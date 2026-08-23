//! Combinators for parsing permutations of sub-parsers.
//!
//! Each `Permute*` combinator accepts any ordering of its components while its serializer always
//! emits the declared order. That makes them deliberately *malleable*: distinct byte strings map to
//! the same value, so [`NonMalleable`](crate::core::proof::NonMalleable) and
//! [`PSRoundTrip`](crate::core::proof::PSRoundTrip) are not available. Soundness is, because
//! reordering preserves the total length.
//!
//! Only widths 2 to 4 are provided. The construction enumerates orderings, so the number of parse
//! paths grows as `N!` (`Permute4` already has 24).
/// Executable parser and serializer implementations for this combinator.
pub mod exec;
/// Proofs of the security and correctness properties for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

use crate::combinators::choice::Alt;
use crate::combinators::Mapped;

verus! {

pub open spec fn swap2<A, B>(i: (B, A)) -> (A, B) {
    (i.1, i.0)
}

pub open spec fn swap3_1<A, B, C>(i: (B, (A, C))) -> (A, (B, C)) {
    (i.1.0, (i.0, i.1.1))
}

pub open spec fn swap3_2<A, B, C>(i: (C, (A, B))) -> (A, (B, C)) {
    (i.1.0, (i.1.1, i.0))
}

pub open spec fn swap4_1<A, B, C, D>(i: (B, (A, (C, D)))) -> (A, (B, (C, D))) {
    (i.1.0, (i.0, i.1.1))
}

pub open spec fn swap4_2<A, B, C, D>(i: (C, (A, (B, D)))) -> (A, (B, (C, D))) {
    (i.1.0, (i.1.1.0, (i.0, i.1.1.1)))
}

pub open spec fn swap4_3<A, B, C, D>(i: (D, (A, (B, C)))) -> (A, (B, (C, D))) {
    (i.1.0, (i.1.1.0, (i.1.1.1, i.0)))
}

/// `Permute2<P1, P2>` parses either `(P1, P2)` or `(P2, P1)` and produces `(P1::PVal, P2::PVal)`
///
/// `Permute2 ::= Alt((P1, P2), Mapped((P2, P1), swap))`
#[derive(Copy)]
pub struct Permute2<P1, P2>(pub P1, pub P2);

impl<P1: Clone, P2: Clone> Clone for Permute2<P1, P2> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(P1::clone, (&self.0,), cloned.0),
            call_ensures(P2::clone, (&self.1,), cloned.1),
    {
        Permute2(self.0.clone(), self.1.clone())
    }
}

/// `Permute3<A, B, C>` parses any permutation of A, B, C and produces `(A::PVal, (B::PVal, C::PVal))`
///
/// ```text
/// Permute3(A, B, C) ::= Alt(
///     (A, Permute2(B, C)),
///     Alt(
///         Mapped((B, Permute2(A, C)), swap2),
///         Mapped((C, Permute2(A, B)), swap3),
///     )
/// )
/// ```
#[derive(Copy)]
pub struct Permute3<A, B, C>(pub A, pub B, pub C);

impl<A: Clone, B: Clone, C: Clone> Clone for Permute3<A, B, C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
            call_ensures(C::clone, (&self.2,), cloned.2),
    {
        Permute3(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

/// `Permute4<A, B, C, D>` parses any permutation and produces `(A::PVal, (B::PVal, (C::PVal, D::PVal)))`
///
/// ```text
/// Permute4(A, B, C, D) ::= Alt(
///     (A, Permute3(B, C, D)),
///     Alt(
///         Mapped((B, Permute3(A, C, D)), swap4_1),
///         Alt(
///             Mapped((C, Permute3(A, B, D)), swap4_2),
///             Mapped((D, Permute3(A, B, C)), swap4_3),
///         )
///     )
/// )
/// ```
#[derive(Copy)]
pub struct Permute4<A, B, C, D>(pub A, pub B, pub C, pub D);

impl<A: Clone, B: Clone, C: Clone, D: Clone> Clone for Permute4<A, B, C, D> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
            call_ensures(C::clone, (&self.2,), cloned.2),
            call_ensures(D::clone, (&self.3,), cloned.3),
    {
        Permute4(self.0.clone(), self.1.clone(), self.2.clone(), self.3.clone())
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::{Permute2, Permute3, Permute4};
    use crate::combinators::{Const, U8};
    use crate::core::exec::{ByteLen, Parser, Prepare, SerializerExt};

    /// A one-byte format that only accepts `b`, so orderings are distinguishable.
    fn tag(b: u8) -> Const<U8, u8> {
        Const(U8, b)
    }

    /// Serializes `$v` with `$fmt`, checking that `prepare` and `length` agree.
    macro_rules! serialized {
        ($fmt:expr, $v:expr) => {{
            let len = $fmt.prepare(&$v).unwrap();
            assert_eq!($fmt.length(&$v), len, "length and prepare disagree");
            let mut out = vec![0u8; len];
            $fmt.serialize(&$v, out.as_mut_slice());
            out
        }};
    }

    #[test]
    fn permute2_accepts_both_orders_and_serializes_the_declared_one() {
        let fmt = Permute2(tag(0xAA), tag(0xBB));
        let value = (0xAAu8, 0xBBu8);

        // Declared order and the swap both parse to the same value: the malleability witness.
        assert_eq!(fmt.parse(&&[0xAA, 0xBB][..]), Ok((2, value)));
        assert_eq!(fmt.parse(&&[0xBB, 0xAA][..]), Ok((2, value)));

        // Serialization always emits the declared order.
        assert_eq!(serialized!(fmt, value), vec![0xAA, 0xBB]);
    }

    #[test]
    fn permute2_rejects_wrong_and_truncated_input() {
        let fmt = Permute2(tag(0xAA), tag(0xBB));
        assert!(fmt.parse(&&[0xAA, 0xAA][..]).is_err());
        assert!(fmt.parse(&&[0xAA][..]).is_err());
        assert!(fmt.parse(&&[][..]).is_err());
    }

    #[test]
    fn permute3_accepts_all_six_orders() {
        let fmt = Permute3(tag(0xA1), tag(0xB2), tag(0xC3));
        let value = (0xA1u8, (0xB2u8, 0xC3u8));

        for order in [
            [0xA1, 0xB2, 0xC3],
            [0xA1, 0xC3, 0xB2],
            [0xB2, 0xA1, 0xC3],
            [0xB2, 0xC3, 0xA1],
            [0xC3, 0xA1, 0xB2],
            [0xC3, 0xB2, 0xA1],
        ] {
            assert_eq!(fmt.parse(&&order[..]), Ok((3, value)), "order {order:02x?}");
        }

        assert_eq!(serialized!(fmt, value), vec![0xA1, 0xB2, 0xC3]);
        assert!(fmt.parse(&&[0xA1, 0xB2, 0xB2][..]).is_err());
        assert!(fmt.parse(&&[0xA1, 0xB2][..]).is_err());
    }

    #[test]
    fn permute4_accepts_every_order() {
        let fmt = Permute4(tag(0xA1), tag(0xB2), tag(0xC3), tag(0xD4));
        let value = (0xA1u8, (0xB2u8, (0xC3u8, 0xD4u8)));

        // All 24 permutations, generated so the test covers each branch of each nesting level.
        let bytes = [0xA1u8, 0xB2, 0xC3, 0xD4];
        let mut count = 0;
        for i in 0..4 {
            for j in 0..4 {
                for k in 0..4 {
                    for l in 0..4 {
                        if i == j || i == k || i == l || j == k || j == l || k == l {
                            continue;
                        }
                        let order = [bytes[i], bytes[j], bytes[k], bytes[l]];
                        assert_eq!(fmt.parse(&&order[..]), Ok((4, value)), "order {order:02x?}");
                        count += 1;
                    }
                }
            }
        }
        assert_eq!(count, 24);

        assert_eq!(serialized!(fmt, value), vec![0xA1, 0xB2, 0xC3, 0xD4]);
        assert!(fmt.parse(&&[0xA1, 0xB2, 0xC3][..]).is_err());
        assert!(fmt.parse(&&[0xA1, 0xB2, 0xC3, 0xC3][..]).is_err());
    }

    #[test]
    fn parsing_consumes_only_the_permutation_and_leaves_trailing_bytes() {
        let fmt = Permute2(tag(0xAA), tag(0xBB));
        let (consumed, value) = fmt.parse(&&[0xBB, 0xAA, 0x99][..]).unwrap();
        assert_eq!(consumed, 2);
        assert_eq!(value, (0xAAu8, 0xBBu8));
    }
}
