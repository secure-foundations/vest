pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Fixed<const N: usize>;

pub struct Varied(pub usize);

pub struct ExactLen<Inner>(pub usize, pub Inner);

pub struct AndThen<A, B>(pub A, pub B);

} // verus!
