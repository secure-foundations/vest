use super::*;
use crate::asn1::*;
/// Define and implement a temporary Eq replacement "PolyfillEq" for some types
use vstd::prelude::*;

verus! {

/// A temporary replacement Clone
pub trait PolyfillEq: View + Sized {
    fn polyfill_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> (self@ == other@);
}

macro_rules! impl_trivial_polyfill_eq {
    ($($t:ty)*) => {
        $(
            ::vstd::prelude::verus! {
                impl PolyfillEq for $t {
                    #[inline(always)]
                    fn polyfill_eq(&self, other: &Self) -> bool {
                        self == other
                    }
                }
            }
        )*
    };
}

impl_trivial_polyfill_eq! {
    bool
    u8 u16 u32 u64 u128
    i8 i16 i32 i64 i128
    usize
}

macro_rules! impl_polyfill_eq_for_slice_vec {
    ($($t:ty)*) => {
        $(
            ::vstd::prelude::verus! {
                impl PolyfillEq for &[$t] {
                    fn polyfill_eq(&self, other: &Self) -> bool {
                        if self.len() != other.len() {
                            return false;
                        }

                        let len = self.len();
                        for i in 0..len
                            invariant
                                len == self@.len(),
                                self@.len() == other@.len(),
                                forall |j| !(0 <= j < i) || self@[j] == other@[j],
                        {
                            if self[i] != other[i] {
                                return false;
                            }
                        }

                        assert(verus_builtin::ext_equal(self@, other@));

                        true
                    }
                }

                impl PolyfillEq for Vec<$t> {
                    fn polyfill_eq(&self, other: &Self) -> bool {
                        self.as_slice().polyfill_eq(&other.as_slice())
                    }
                }
            }
        )*
    };
}

impl_polyfill_eq_for_slice_vec! {
    bool
    u8 u16 u32 u64 u128
    i8 i16 i32 i64 i128
    usize
}

impl<T: PolyfillEq> PolyfillEq for VecDeep<T> {
    fn polyfill_eq(&self, other: &Self) -> (res: bool)
    {
        if self.len() != other.len() {
            return false;
        }

        let len = self.len();
        for i in 0..len
            invariant
                len == self@.len(),
                self@.len() == other@.len(),
                forall |j| 0 <= j < i ==> self@[j] == other@[j],
        {
            if !self.get(i).polyfill_eq(&other.get(i)) {
                return false;
            }
        }

        assert(self@ =~= other@);

        true
    }
}

impl<U: PolyfillEq, V: PolyfillEq> PolyfillEq for Either<U, V> {
    #[inline(always)]
    fn polyfill_eq(&self, other: &Self) -> (res: bool) {
        match (self, other) {
            (Either::Left(a), Either::Left(b)) => a.polyfill_eq(b),
            (Either::Right(a), Either::Right(b)) => a.polyfill_eq(b),
            _ => false,
        }
    }
}

impl PolyfillEq for NullValue {
    #[inline(always)]
    fn polyfill_eq(&self, _other: &Self) -> (res: bool) {
        true
    }
}

impl PolyfillEq for EndValue {
    #[inline(always)]
    fn polyfill_eq(&self, _other: &Self) -> (res: bool) {
        true
    }
}

}
