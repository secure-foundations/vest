//! Byte-aligned bitfield specification and proof combinator.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::{PredFnSpec, SpecByteLen};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(Tuple)]
#[verifier::reject_recursive_types(Nominal)]
/// Packs a tuple of logical bitfield values into one fixed-width integer representation.
///
/// Generated Vest bitfield formats use the functions stored here to unpack the
/// wire integer, validate the structural tuple, construct the public nominal
/// value, and perform the inverse operation during serialization.
pub struct Bits<Repr: SpecByteLen, Tuple, Nominal> {
    /// Integer format that reads and writes the complete bitfield word.
    pub repr: Repr,
    /// Splits the representation into its structural field tuple.
    pub unpack: spec_fn(Repr::T) -> Tuple,
    /// Packs the structural field tuple into the representation.
    pub pack: spec_fn(Tuple) -> Repr::T,
    /// Predicate enforcing field widths and reserved-bit constraints.
    pub refinement: PredFnSpec<Tuple>,
    /// Constructs the public nominal value from structural fields.
    pub ctor: spec_fn(Tuple) -> Nominal,
    /// Projects a public nominal value back to structural fields.
    pub dtor: spec_fn(Nominal) -> Tuple,
    /// Additional consistency predicate for nominal values.
    pub consistent: PredFnSpec<Nominal>,
}

} // verus!
