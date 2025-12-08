pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

/// A combinator that parses a prefix combinator followed by a main combinator,
/// but only returns the result of the main combinator.
/// Preceded(A, B) parses A then B, but returns only B's value.
pub struct Preceded<A, B>(pub A, pub B);

} // verus!
