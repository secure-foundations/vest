use super::bytes::{Variable, Fixed, Tail};
use super::tag::Tag;
use super::uints::{U16Le, U32Le, U64Le, U8};
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

impl_reflexive_clone!(U8, U16Le, U32Le, U64Le, Tail);

// macro_rules! impl_clone_for_int_tags {
//     ($($combinator:ty),*) => {
//         ::builtin_macros::verus! {
//             $(
//                 impl Clone for $combinator {
//                     fn clone(&self) -> (out: Self)
//                         ensures
//                             out == *self,
//                     {
//                         Tag::new(self.0.inner.clone(), self.0.predicate.0)
//                     }
//                 }
//             )*
//         }
//     };
// }
// impl_clone_for_int_tags!(Tag<U8, u8>, Tag<U16Le, u16>, Tag<U32Le, u32>, Tag<U64Le, u64>);
// impl<T: FromToBytes + Copy> Clone for Tag<Int<T>, T> {
//     fn clone(&self) -> (out: Self)
//         ensures
//             out == *self,
//     {
//         Tag::new(self.0.inner.clone(), self.0.predicate.0)
//     }
// }
//
impl<'a> Clone for Tag<Variable, &'a [u8]> {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Tag::new(self.0.inner.clone(), self.0.predicate.0)
    }
}

impl<'a, const N: usize> Clone for Tag<Fixed<N>, &'a [u8]> {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Tag::new(self.0.inner.clone(), self.0.predicate.0)
    }
}

impl Clone for Variable {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Variable(self.0)
    }
}

impl<const N: usize> Clone for Fixed<N> {
    fn clone(&self) -> (out: Self)
        ensures
            out == *self,
    {
        Fixed
    }
}

} // verus!
