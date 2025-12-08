pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

/// A combinator that parses a main combinator followed by a suffix combinator,
/// but only returns the result of the main combinator.
/// Terminated(A, B) parses A then B, but returns only A's value.
pub struct Terminated<A, B>(pub A, pub B);

} // verus!
