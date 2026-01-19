pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Star<A> {
    pub inner: A,
}

pub struct Repeat<A, B>(pub A, pub B);

} // verus!
