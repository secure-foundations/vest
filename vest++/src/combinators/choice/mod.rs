pub mod proof;
pub mod spec;

pub use spec::Either;

use vstd::prelude::*;

verus! {

pub struct Choice<A, B>(pub A, pub B);

} // verus!
