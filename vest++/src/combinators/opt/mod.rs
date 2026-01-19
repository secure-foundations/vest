pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Opt<A>(pub A);

pub struct Optional<A, B>(pub A, pub B);

} // verus!
