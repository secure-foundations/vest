pub mod proof;
pub mod spec;

use vstd::prelude::*;

pub use spec::Either;

verus! {

pub struct Choice<A, B>(pub A, pub B);

} // verus!
