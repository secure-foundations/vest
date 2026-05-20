//! Conditional combinator: enabled or disabled by a boolean flag.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Conditionally apply `Inner` depending on a boolean flag.
///
/// Parsing semantics: if the flag is `true`, parse with `Inner` and return its value; if the flag is `false`, fail.
///
/// ## Consistency
///
/// A value `v` is consistent with `Cond(true, Inner)` iff it is consistent with `Inner`. No value is consistent with `Cond(false, Inner)`.
pub struct Cond<Inner>(pub bool, pub Inner);

} // verus!
