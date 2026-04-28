//! Name-carrying wrapper for runtime parser error reporting.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use vstd::prelude::*;

verus! {

/// Transparent wrapper around `Inner` that annotates runtime parse errors with a static format
/// name.
///
/// The semantic format is unchanged: parsing, consistency, serialization, and all proof
/// obligations are delegated to `Inner`.
pub struct Named<Inner>(pub Inner, pub &'static str);

impl<Inner: LeafNonMalleable> LeafNonMalleable for Named<Inner> {
    proof fn nonmal_leaf_inv(&self) {
        self.0.nonmal_leaf_inv();
    }
}

} // verus!
