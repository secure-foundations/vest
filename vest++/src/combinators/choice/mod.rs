pub mod spec;
pub mod proof;

pub use spec::Either;

use vstd::prelude::*;

verus! {

pub struct Choice<A, B>(pub A, pub B);

} // verus!
