use super::*;
/// Define and implement a temporary Clone replacement "PolyfillClone" for some types
use vstd::prelude::*;

verus! {

/// A temporary replacement Clone
pub trait PolyfillClone: View + Sized {
    fn clone(&self) -> (res: Self)
        ensures
            res@ == self@;
}

impl PolyfillClone for bool {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a> PolyfillClone for &'a str {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> PolyfillClone for &'a [T] {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for usize {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for u8 {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for u16 {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

// Can't do this due to https://github.com/verus-lang/verus/issues/1108
// impl PolyfillClone for () {
//     fn clone(&self) -> Self {
//         ()
//     }
// }

impl<T: Copy> PolyfillClone for Vec<T> {
    /// We trust the builtin Vec::clone implementation
    #[verifier::external_body]
    #[inline(always)]
    fn clone(&self) -> Self {
        Clone::clone(self)
    }
}

impl<T1: PolyfillClone, T2: PolyfillClone> PolyfillClone for (T1, T2) {
    #[inline(always)]
    fn clone(&self) -> Self {
        (self.0.clone(), self.1.clone())
    }
}

impl<T1: PolyfillClone, T2: PolyfillClone> PolyfillClone for Either<T1, T2> {
    #[inline(always)]
    fn clone(&self) -> Self {
        match self {
            Either::Left(v) => Either::Left(v.clone()),
            Either::Right(v) => Either::Right(v.clone()),
        }
    }
}

impl<T: PolyfillClone> PolyfillClone for RepeatResult<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        let mut items: Vec<T> = Vec::with_capacity(self.0.len());

        for i in 0..self.0.len()
            invariant
                items.len() == i,
                forall |j| #![auto] 0 <= j < i ==> items[j]@ == self.0[j]@,
        {
            items.push(self.0[i].clone());
        }

        proof {
            assert(items.len() == self.0.len());
            assert(forall |j| #![auto] 0 <= j < items.len() ==> items[j]@ == self.0[j]@);
            assume(RepeatResult(items)@ == self@);
        }

        RepeatResult(items)
    }
}

}
