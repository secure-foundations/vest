use super::bytes::{Fixed, Tail, Variable};
use super::uints::{U16Le, U32Le, U64Le, U8};
use vstd::prelude::*;

verus! {

macro_rules! impl_reflexive_clone {
    ($($ty:ty),*) => {
        ::vstd::prelude::verus! {
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
