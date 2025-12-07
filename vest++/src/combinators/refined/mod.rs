pub mod proof;
pub mod spec;

use crate::core::spec::SpecType;
use vstd::prelude::*;

verus! {

pub struct Refined<A: SpecType> {
    pub inner: A,
    pub pred: spec_fn(A::Type) -> bool,
}

} // verus!
