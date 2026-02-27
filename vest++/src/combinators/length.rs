//! The length abstraction [`AsLen`] for types usable as format length (or count) fields.
//!
//! Implemented for [`u8`], [`u16`], [`u32`], and [`usize`].
use vstd::prelude::*;

verus! {

/// Types that can serve as format length (or count) fields, with proof of lossless
/// `usize`/`nat` conversions.
pub trait AsLen: Sized {
    /// Convert to `usize`.
    spec fn as_usize(self) -> usize;

    /// Construct from a `nat`.
    spec fn from_nat(n: nat) -> Self;

    /// `from_nat(v.as_usize() as nat) == v`.
    proof fn lemma_lossless_casting(v: Self)
        ensures
            Self::from_nat(v.as_usize() as nat) == v,
    ;
}

impl AsLen for u8 {
    open spec fn as_usize(self) -> usize {
        self as usize
    }

    open spec fn from_nat(n: nat) -> Self {
        n as u8
    }

    proof fn lemma_lossless_casting(v: Self) {
    }
}

impl AsLen for u16 {
    open spec fn as_usize(self) -> usize {
        self as usize
    }

    open spec fn from_nat(n: nat) -> Self {
        n as u16
    }

    proof fn lemma_lossless_casting(v: Self) {
    }
}

impl AsLen for u32 {
    open spec fn as_usize(self) -> usize {
        self as usize
    }

    open spec fn from_nat(n: nat) -> Self {
        n as u32
    }

    proof fn lemma_lossless_casting(v: Self) {
    }
}

impl AsLen for usize {
    open spec fn as_usize(self) -> usize {
        self
    }

    open spec fn from_nat(n: nat) -> Self {
        n as usize
    }

    proof fn lemma_lossless_casting(v: Self) {
    }
}

} // verus!
