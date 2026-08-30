/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::{PredFnSpec, SpecByteLen};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(Tuple)]
#[verifier::reject_recursive_types(Nominal)]
pub struct Bits<Repr: SpecByteLen, Tuple, Nominal> {
    pub repr: Repr,
    pub unpack: spec_fn(Repr::T) -> Tuple,
    pub pack: spec_fn(Tuple) -> Repr::T,
    pub refinement: PredFnSpec<Tuple>,
    pub ctor: spec_fn(Tuple) -> Nominal,
    pub dtor: spec_fn(Nominal) -> Tuple,
    pub consistent: PredFnSpec<Nominal>,
}

} // verus!
