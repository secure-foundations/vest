pub mod proof;
pub mod spec;

use vstd::prelude::*;

pub use spec::Sum;

verus! {

pub struct Choice<A, B>(pub A, pub B);

pub struct Alt<A, B>(pub A, pub B);

} // verus!
