//! BER-encoded boolean combinator.

/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// BER Boolean combinator: FALSE = `0x00`, TRUE = any non-zero byte.
///
/// ## Malleability
///
/// This is a *malleable* combinator: it accepts multiple byte representations for `true`.
pub struct BerBool;

} // verus!
