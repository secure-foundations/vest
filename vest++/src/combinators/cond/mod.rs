pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

/// Conditionally apply `Inner` depending on a boolean flag.
///
/// - if `self.0` is `true`, this combinator behaves like `Inner`
/// - if `self.0` is `false`, parsing fails and serialization is disallowed
pub struct Cond<Inner>(pub bool, pub Inner);

} // verus!
