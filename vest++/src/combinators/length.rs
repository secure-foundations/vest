//! The length abstraction [`AsLen`] for types usable as format length (or count) fields.
//!
//! Implemented for [`u8`], [`u16`], [`u32`], and [`usize`].
use vstd::prelude::*;

verus! {

/// Types that can serve as format length (or count) fields.
///
/// The spec-facing conversion is to `nat`, which is the natural domain for lengths in proofs. The
/// exec-facing conversion is to `usize`, which is the natural domain for runtime indexing.
pub trait AsLen: Sized + Copy {
    /// The mathematical length represented by this value.
    spec fn as_nat(self) -> nat;

    /// The runtime length represented by this value.
    fn as_usize(self) -> (len: usize)
        ensures
            len as nat == self.as_nat(),
    ;

    /// Construct from a `nat`.
    ///
    /// This is total for convenience, but the roundtrip law from `nat` only holds when
    /// `fits_nat(n)` is true.
    spec fn from_nat(n: nat) -> Self;

    /// `from_nat(v.as_nat()) == v`.
    proof fn lemma_lossless_casting(v: Self)
        ensures
            Self::from_nat(v.as_nat()) == v,
    ;
}

} // verus!
macro_rules! impl_as_len_for_uint {
    ($ty:ty) => {
        verus! {
            impl AsLen for $ty {
                open spec fn as_nat(self) -> nat {
                    self as nat
                }

                fn as_usize(self) -> (len: usize) {
                    self as usize
                }

                open spec fn from_nat(n: nat) -> Self {
                    n as $ty
                }

                proof fn lemma_lossless_casting(v: Self) {
                }
            }
        }
    };
}

impl_as_len_for_uint!(u8);
impl_as_len_for_uint!(u16);
impl_as_len_for_uint!(u32);
impl_as_len_for_uint!(usize);
