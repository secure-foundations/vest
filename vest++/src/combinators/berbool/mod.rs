pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

/// BER Boolean combinator: parses/serializes boolean values where FALSE is 0x00
/// and TRUE can be any non-zero byte.
///
/// This combinator is malleable because TRUE has multiple representations.
pub struct BerBool;

} // verus!
