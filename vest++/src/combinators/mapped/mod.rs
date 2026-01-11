pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Mapped<Inner, M> {
    pub inner: Inner,
    pub mapper: M,
}

} // verus!
