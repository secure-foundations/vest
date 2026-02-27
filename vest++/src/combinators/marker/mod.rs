//! Marker combinators: unit (`Empty`) and uninhabitable (`Void`).
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Marker combinator that denotes the "empty" format.
///
/// Parsing semantics: always succeeds without consuming any input, returning `()`.
///
/// Serialization semantics: produces an empty byte sequence.
pub struct Empty;

/// Marker combinator that denotes the "void" format.
///
/// Parsing semantics: always fails.
///
/// ## Consistency
///
/// No value is consistent with `Void`.
pub struct Void;

} // verus!
