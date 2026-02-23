pub mod proof;
pub mod spec;

use vstd::prelude::*;

verus! {

pub struct Tail;

pub struct Eof;

pub struct OptionalEof<C>(pub C);

pub struct RepeatUtilEof<C>(pub C);

} // verus!
