//! Value refinement and constant-value combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::SpecByteLen;
use vstd::prelude::*;

verus! {

/// Value refinement combinator: filters values through a predicate.
///
/// ## Consistency
///
/// `inner.consistent(v) && predicate.apply(v)`.
pub struct Refined<Inner, Predicate>(pub Inner, pub Predicate);

/// Constant-value combinator: matches a specific constant value.
///
/// Parsing semantics: parses with `inner` and succeeds only if the result equals the expected value.
/// The matched constant value itself is returned.
///
/// Implements [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal).
pub struct Const<Inner, Value>(pub Inner, pub Value);

/// Sugar for `Preceded { a: Const(inner, tag), a_val: tag, b: body }`.
pub struct WithPrefixTag<Tg: SpecByteLen, Of>(pub Tg, pub Tg::T, pub Of);

/// Sugar for `Terminated { a: body, b: Const(inner, tag), b_val: tag }`.
pub struct WithSuffixTag<Tg: SpecByteLen, Of>(pub Tg, pub Tg::T, pub Of);

} // verus!
/// Backward-compatible name for [`WithPrefixTag`].
pub use WithPrefixTag as Tagged;
