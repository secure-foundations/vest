//! Executable parsing and serialization.
pub mod error;
pub mod fns;
pub mod input;
pub mod parser;
pub mod serializer;

pub use error::{ParseError, ParseErrorKind};

use vstd::prelude::*;

verus! {

/// Executable equality that is tied to `DeepView` equality.
pub trait DeepEq: PartialEq + DeepView {
    fn deep_eq(&self, other: &Self) -> (eq: bool)
        ensures
            eq == (self.deep_view() == other.deep_view()),
    ;
}

pub trait SelfView: DeepEq<V = Self> + Sized {
    fn eq(&self, other: &Self) -> (eq: bool)
        ensures
            eq == (self == other),
    ;
}

macro_rules! impl_self_view_for {
    ($($t:ty),*) => {
        $(
            impl DeepEq for $t {
                fn deep_eq(&self, other: &Self) -> bool {
                    *self == *other
                }
            }
            impl SelfView for $t {
                fn eq(&self, other: &Self) -> bool {
                    *self == *other
                }
            }
        )*
    };
}

impl_self_view_for!(u8, u16, u32, u64, usize, bool, ());

#[verifier::external_body]
#[inline(always)]
pub fn cmp_byte_slices(a: &[u8], b: &[u8]) -> (r: bool)
    requires
        a.len() == b.len(),
    ensures
        r == (a@ == b@),
        r == (a.deep_view() == b.deep_view()),
{
    a == b
}

impl DeepEq for &[u8] {
    fn deep_eq(&self, other: &Self) -> (eq: bool) {
        if self.len() != other.len() {
            assert(self.deep_view().len() != other.deep_view().len());
            false
        } else {
            cmp_byte_slices(self, other)
        }
    }
}

impl<const N: usize> DeepEq for [u8; N] {
    fn deep_eq(&self, other: &Self) -> (eq: bool) {
        cmp_byte_slices(self.as_slice(), other.as_slice())
    }
}

impl DeepEq for Vec<u8> {
    fn deep_eq(&self, other: &Self) -> (eq: bool) {
        if self.len() != other.len() {
            assert(self.deep_view().len() != other.deep_view().len());
            false
        } else {
            cmp_byte_slices(self.as_slice(), other.as_slice())
        }
    }
}

} // verus!
