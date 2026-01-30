pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

/// Combinator for parsing and serializing an unsigned 8-bit integer.
pub struct U8;

/// Combinator for parsing and serializing a little-endian unsigned 16-bit integer.
pub struct U16Le;

/// Combinator for parsing and serializing a big-endian unsigned 16-bit integer.
pub struct U16Be;

/// Combinator for parsing and serializing a little-endian unsigned 32-bit integer.
pub struct U32Le;

/// Combinator for parsing and serializing a big-endian unsigned 32-bit integer.
pub struct U32Be;

} // verus!
