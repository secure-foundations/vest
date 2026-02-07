pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Fixed<const N: usize>;

pub struct Varied(pub usize);

} // verus!
