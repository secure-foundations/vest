pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Star<A> {
    pub inner: A,
}

pub struct Repeat<A, B>(pub A, pub B);

pub struct RepeatN<C, N = u8>(pub N, pub C);

pub struct Array<const N: usize, C>(pub C);

} // verus!
