extern crate alloc;
use vstd::prelude::*;
use vstd::slice::slice_index_get;

use crate::regular::uints::FromToBytes;

verus! {

/// Spec version of [`From`].
pub trait SpecFrom<T>: Sized {
    /// Spec version of [`From::ex_from`]
    spec fn spec_from(t: T) -> Self;
}

/// Spec version of [`Into`].
pub trait SpecInto<T>: Sized {
    /// Spec version of [`Into::ex_into`]
    spec fn spec_into(self) -> T;
}

impl<T, U> SpecInto<U> for T where U: SpecFrom<T> {
    open spec fn spec_into(self) -> U {
        U::spec_from(self)
    }
}

impl<T> SpecFrom<T> for T {
    open spec fn spec_from(t: T) -> T {
        t
    }
}

/// Vest equivalent of [`std::convert::From`].
pub trait From<T> where T: View, Self: View + Sized, Self::V: SpecFrom<T::V> {
    /// Vest equivalent of [`std::convert::From::from`].
    fn ex_from(t: T) -> (res: Self)
        ensures
            res@ == Self::V::spec_from(t@),
    ;
}

/// Vest equivalent of [`std::convert::Into`].
pub trait Into<T> where T: View, Self: View + Sized, Self::V: SpecInto<T::V> {
    /// Vest equivalent of [`std::convert::Into::into`].
    fn ex_into(self) -> (res: T)
        ensures
            res@ == self@.spec_into(),
    ;
}

impl<T, U> Into<U> for T where T: View, U: View, U: From<T>, U::V: SpecFrom<T::V> {
    fn ex_into(self) -> U {
        U::ex_from(self)
    }
}

impl<T> From<T> for T where T: View, T::V: SpecFrom<T::V> {
    fn ex_from(t: T) -> (res: T) {
        t
    }
}

impl<const N: usize, 'a, 'b> From<&'a [u8; N]> for &'b [u8] where 'a: 'b {
    fn ex_from(v: &'a [u8; N]) -> &'b [u8] {
        v.as_slice()
    }
}

/// A helper trait for two different types that can be compared.
pub trait Compare<Other> where Self: View, Other: View<V = Self::V> {
    /// Compare a value of `Self` with a value of `Other`.
    fn compare(&self, other: &Other) -> (o: bool)
        ensures
            o == (self@ == other@),
    ;
}

impl<Int: FromToBytes> Compare<Int> for Int {
    fn compare(&self, other: &Int) -> bool {
        self.eq(other)
    }
}

impl<'a, 'b> Compare<&'b [u8]> for &'a [u8] {
    fn compare(&self, other: &&'b [u8]) -> bool {
        compare_slice(self, *other)
    }
}

/// Helper function to splice a sequence of bytes into another sequence of bytes.
pub open spec fn seq_splice(data: Seq<u8>, pos: usize, v: Seq<u8>) -> Seq<u8>
    recommends
        pos + v.len() <= data.len(),
{
    data.subrange(0, pos as int).add(v).add(data.subrange(pos + v.len() as int, data.len() as int))
}

/// Helper function to set a range of bytes in a vector.
pub fn set_range<'a>(data: &mut Vec<u8>, i: usize, input: &[u8])
    requires
        0 <= i + input@.len() <= old(data)@.len() <= usize::MAX,
    ensures
        data@.len() == old(data)@.len() && data@ == old(data)@.subrange(0, i as int).add(
            input@,
        ).add(old(data)@.subrange(i + input@.len(), data@.len() as int)),
{
    let mut j = 0;
    while j < input.len()
        invariant
            data@.len() == old(data)@.len(),
            forall|k| 0 <= k < i ==> data@[k] == old(data)@[k],
            forall|k| i + input@.len() <= k < data@.len() ==> data@[k] == old(data)@[k],
            0 <= i <= i + j <= i + input@.len() <= data@.len() <= usize::MAX,
            forall|k| 0 <= k < j ==> data@[i + k] == input@[k],
    {
        data.set(i + j, *slice_index_get(input, j));
        j = j + 1
    }
    assert(data@ =~= old(data)@.subrange(0, i as int).add(input@).add(
        old(data)@.subrange(i + input@.len(), data@.len() as int),
    ))
}

/// Helper function to compare two slices.
pub fn compare_slice<'a, 'b>(x: &'a [u8], y: &'a [u8]) -> (res: bool)
    ensures
        res == (x@ == y@),
{
    if x.len() != y.len() {
        assert(x@.len() != y@.len());
        return false;
    }
    for i in 0..x.len()
        invariant
            0 <= i <= x.len(),
            x.len() == y.len(),
            forall|j: int| 0 <= j < i ==> x@[j] == y@[j],
    {
        if slice_index_get(x, i) != slice_index_get(y, i) {
            assert(x@[i as int] != y@[i as int]);
            return false;
        }
    }
    proof {
        assert(x@ =~= y@);
    }
    true
}

/// Helper trait for types that have a reflexive view.
pub trait ViewReflex where Self: std::marker::Sized + View<V = Self> {
    /// Reflexivity proof for the view.
    proof fn reflex(&self)
        ensures
            self@ == self,
    ;
}

/// Helper function to initialize a vector of `u8` with zeros.
pub exec fn init_vec_u8(n: usize) -> (res: Vec<u8>)
    ensures
        res@.len() == n,
{
    let mut i: usize = 0;
    let mut ret: Vec<u8> = Vec::new();
    while i < n
        invariant
            0 <= i <= n,
            ret@.len() == i,
    {
        ret.push(0);
        assert(ret@[i as int] == 0);
        i = i + 1
    }
    ret
}

} // verus!
macro_rules! declare_identity_view_reflex {
    ($t:ty) => {
        ::builtin_macros::verus! {
            impl ViewReflex for $t {
                proof fn reflex(&self) {}
            }
        }
};
}

declare_identity_view_reflex!(());

declare_identity_view_reflex!(bool);

declare_identity_view_reflex!(u8);

declare_identity_view_reflex!(u16);

declare_identity_view_reflex!(u32);

declare_identity_view_reflex!(u64);

declare_identity_view_reflex!(u128);

declare_identity_view_reflex!(usize);

declare_identity_view_reflex!(i8);

declare_identity_view_reflex!(i16);

declare_identity_view_reflex!(i32);

declare_identity_view_reflex!(i64);

declare_identity_view_reflex!(i128);

declare_identity_view_reflex!(isize);
