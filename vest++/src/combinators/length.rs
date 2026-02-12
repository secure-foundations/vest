use vstd::prelude::*;

verus! {

/// Types that can safely act as format length (or count) fields.
pub trait AsLen: Sized {
    /// Use as the machine integer `usize`
    spec fn as_usize(self) -> usize;

    /// Get the machine integer value from an abstract natural number
    spec fn from_nat(n: nat) -> Self;

    /// The conversion from Self to usize and back is lossless
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
