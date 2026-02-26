//! Bounded fixpoint combinator for recursive formats.

/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

pub use spec::RecBody;

verus! {

/// Bounded fixpoint combinator: recursive format up to `LIMIT` levels of nesting.
///
/// Parsing semantics: parses with `Body`, which may recursively refer to `Fix` (up to `LIMIT` times).
///
/// TODO: this combinator currently only supports parsing; we should add serialization support as well.
pub struct Fix<const LIMIT: usize, Body>(pub Body);

} // verus!
