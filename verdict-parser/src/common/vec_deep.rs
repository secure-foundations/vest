use super::*;
use vstd::prelude::*;

verus! {

/// A wrapper for Vec with its View implemented
/// one layer deeper than the original Vec
///
/// Otherwise inherits all methods from Vec
#[derive(Debug, Eq, PartialEq)]
pub struct VecDeep<T>(pub Vec<T>);

impl<T: View> View for VecDeep<T> {
    type V = Seq<T::V>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.0.len() as nat, |i: int| self.0@[i]@)
    }
}

/// Cloning VecDeep clones each element
impl<T: PolyfillClone> PolyfillClone for VecDeep<T> where
{
    /// Same as clone of Vec, but this is a "deep" copy
    fn clone(&self) -> Self {
        let mut cloned: Vec<T> = Vec::with_capacity(self.len());

        for i in 0..self.0.len()
            invariant
                cloned.len() == i,
                forall |j| 0 <= j < i ==> cloned[j]@ == #[trigger] self.0[j]@,
        {
            cloned.push(self.0[i].clone());
        }

        assert(VecDeep(cloned)@ =~= self@);

        VecDeep(cloned)
    }
}

impl<T: View> VecDeep<T> {
    #[inline(always)]
    pub fn new() -> (res: Self)
        ensures
            res@ =~= Seq::<T::V>::empty(),
    {
        VecDeep(Vec::new())
    }

    #[inline(always)]
    pub fn with_capacity(cap: usize) -> (res: Self)
        ensures
            res@ =~= Seq::<T::V>::empty(),
    {
        VecDeep(Vec::with_capacity(cap))
    }

    #[inline(always)]
    pub fn push(&mut self, value: T)
        ensures
            self@ =~= old(self)@.push(value@)
    {
        self.0.push(value);
    }

    #[inline(always)]
    pub fn len(&self) -> (res: usize)
        ensures
            res == self@.len()
    {
        self.0.len()
    }

    #[inline(always)]
    pub fn get(&self, i: usize) -> (res: &T)
        requires
            i < self@.len(),
        ensures
            res@ == self@[i as int],
    {
        &self.0[i]
    }

    #[inline(always)]
    pub fn remove(&mut self, i: usize) -> (res: T)
        requires
            i < old(self)@.len(),
        ensures
            res@ =~= old(self)@[i as int],
            self@ =~= old(self)@.remove(i as int),
    {
        self.0.remove(i)
    }

    #[inline(always)]
    pub fn append(&mut self, other: &mut VecDeep<T>)
        ensures
            self@ =~= old(self)@ + old(other)@,
            other@ =~= Seq::<T::V>::empty(),
    {
        self.0.append(&mut other.0);
    }

    #[inline(always)]
    pub fn append_owned(&mut self, mut other: VecDeep<T>)
        ensures
            self@ =~= old(self)@ + other@,
    {
        self.0.append(&mut other.0);
    }

    // #[verifier::external_body]
    // #[inline(always)]
    // pub fn flatten(v: VecDeep<VecDeep<T>>) -> (res: VecDeep<T>)
    //     ensures res@ == v@.flatten()
    // {
    //     Self::from_vec(v.0.into_iter().map(|u| u.0).flatten().collect())
    // }

    #[inline(always)]
    pub fn split_off(&mut self, at: usize) -> (res: VecDeep<T>)
        requires
            at <= old(self)@.len(),
        ensures
            self@ =~= old(self)@.subrange(0, at as int),
            res@ =~= old(self)@.subrange(at as int, old(self)@.len() as int),
    {
        VecDeep(self.0.split_off(at))
    }

    #[inline(always)]
    pub fn from_vec(v: Vec<T>) -> (res: Self)
        ensures
            res@ =~= VecDeep(v)@,
    {
        VecDeep(v)
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn from_slice(slice: &[T]) -> (res: Self)
        where T: Copy
        ensures
            res@ =~= slice@.map_values(|x: T| x@),
    {
        VecDeep(slice.to_vec())
    }

    #[inline(always)]
    pub fn to_vec_owned(self) -> (res: Vec<T>)
        ensures
            self@ =~= VecDeep(res)@,
    {
        self.0
    }

    #[inline(always)]
    pub fn to_vec(&self) -> (res: &Vec<T>)
        ensures
            self@ =~= VecDeep(*res)@,
    {
        &self.0
    }
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! vec_deep {
    ($($x:tt)*) => {
        VecDeep::from_vec(vec![$($x)*])
    };
}
pub use vec_deep;

}
