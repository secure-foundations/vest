pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Fixed<const N: usize>;

pub struct Varied<Len = u8>(pub Len);

pub struct ExactLen<Inner, Len = u8>(pub Len, pub Inner);

pub struct AndThen<A, B>(pub A, pub B);

} // verus!
