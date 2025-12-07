pub mod proof;
pub mod spec;

use crate::core::spec::SpecCombinator;
use vstd::prelude::*;

verus! {

pub struct Refined<A: SpecCombinator> {
    pub inner: A,
    pub pred: spec_fn(A::Type) -> bool,
}

} // verus!
