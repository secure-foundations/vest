use super::bytes::Bytes;
use super::bytes_n::BytesN;
use super::tag::Tag;
use super::tail::Tail;
use super::uints::{U16, U32, U64, U8};
use vstd::prelude::*;

verus! {

macro_rules! impl_reflexive_clone {
    ($($ty:ty),*) => {
        ::builtin_macros::verus! {
            $(
                impl Clone for $ty {
                    fn clone(&self) -> (out: Self)
                        ensures
                            out == *self,
                    {
                        Self
                    }
                }
            )*
        }
    };
}

impl_reflexive_clone!(U8, U16, U32, U64, Tail);

macro_rules! impl_clone_for_int_tags {
    ($($combinator:ty),*) => {
        ::builtin_macros::verus! {
            $(
                impl Clone for $combinator {
                    fn clone(&self) -> (out: Self)
                        ensures
                            out == *self,
                    {
                        Tag::new(self.0.inner.clone(), self.0.predicate.0)
                    }
                }
            )*
        }
    };
}

impl_clone_for_int_tags!(Tag<U8, u8>, Tag<U16, u16>, Tag<U32, u32>, Tag<U64, u64>);

// impl<T: FromToBytes + Copy> Clone for Tag<Int<T>, T> {
//     fn clone(&self) -> (out: Self)
//         ensures
//             out == *self,
//     {
//         Tag::new(self.0.inner.clone(), self.0.predicate.0)
//     }
// }
//
impl<'a> Clone for Tag<Bytes, &'a [u8]> {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Tag::new(self.0.inner.clone(), self.0.predicate.0)
    }
}

impl<'a, const N: usize> Clone for Tag<BytesN<N>, &'a [u8]> {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Tag::new(self.0.inner.clone(), self.0.predicate.0)
    }
}

impl Clone for Bytes {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Bytes(self.0)
    }
}

impl<const N: usize> Clone for BytesN<N> {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        BytesN
    }
}

} // verus!
