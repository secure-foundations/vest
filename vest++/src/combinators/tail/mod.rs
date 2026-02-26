//! Tail-position combinators.

/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Tail combinator: denotes the "tail" of the format, useful for under-specification.
///
/// Parsing semantics: consumes and return all remaining bytes (even if the input is empty).
///
/// ## Note
///
/// The DPS serialization replaces (not prepends to) the output buffer,
/// so `Tail` should only appear at the end of a format (and the trait system enforces this).
pub struct Tail;

/// End-of-file combinator: denotes the "EOF".
///
/// Parsing semantics: succeeds only if the input is empty, producing `()`.
///
/// Implements [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal).
///
/// ## Note
///
/// The DPS serialization always replaces the output buffer with the empty sequence, so `Eof`
/// should only appear at the end of a format (and the trait system enforces this).
pub struct Eof;

/// Sugar for `Optional(C, Eof)`.
pub struct OptionalEof<C>(pub C);

/// Sugar for `Repeat(C, Eof)`.
pub struct RepeatUtilEof<C>(pub C);

} // verus!
