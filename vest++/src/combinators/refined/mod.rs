pub mod spec;
pub mod proof;

use vstd::prelude::*;
use crate::core::spec::SpecCombinator;

verus! {

pub struct Refined<A: SpecCombinator> {
    pub inner: A,
    pub pred: spec_fn(A::Type) -> bool,
}

} // verus!
