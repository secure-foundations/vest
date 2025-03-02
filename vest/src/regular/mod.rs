#![allow(unused)]
/// Builder combinator
pub mod builder;
/// Bytes combinators
pub mod bytes;
/// Uints combinators
pub mod uints;
/// Sequencing combinators
pub mod sequence;
/// Repetition combinators
pub mod repetition;
/// Variant combinators
#[allow(missing_docs)]
pub mod variant;
/// Combinator modifiers
pub mod modifier;
/// Disjointness for Choice combinator
pub mod disjoint;
/// impl Clone for some combinators
pub mod clone;
/// Fail combinator
pub mod fail;
/// Success combinator
pub mod success;
/// Tag combinator
pub mod tag;
/// LEB128-encoded integers
pub mod leb128;
