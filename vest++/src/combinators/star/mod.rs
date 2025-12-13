pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Star<A> {
    pub inner: A,
}

} // verus!
