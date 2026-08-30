//! Conditional format controlled by a boolean flag.
//!
//! A disabled [`Cond`] accepts and serializes no values; an enabled one
//! delegates its specifications, executable operations, and proofs to its child.
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
#[derive(Copy)]
pub struct Cond<Inner>(pub bool, pub Inner);

impl<Inner: Clone> Clone for Cond<Inner> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.1,), cloned.1),
    {
        Cond(self.0, self.1.clone())
    }
}

} // verus!
