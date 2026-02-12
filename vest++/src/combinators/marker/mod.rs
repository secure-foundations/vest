pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

/// Marker combinator that always parses successfully without consuming input.
/// Serializes to the empty byte sequence.
pub struct Empty;

/// Marker combinator that never parses successfully and has no inhabitable values.
pub struct Void;

} // verus!
