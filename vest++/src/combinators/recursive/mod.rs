pub mod spec;

use vstd::prelude::*;

verus! {

/// The "fixpoint" combinator for recursive parser/serializer.
///
/// ## Usage:
///
/// ```rust
/// let parser = Fix(|rec|
///     |i|
///         Mapped {
///             inner: Choice(
///                 Terminated(
///                     Preceded(Tag { inner: U8, tag: 0x7B }, rec),
///                     Tag { inner: U8, tag: 0x7D},
///                 ),
///                 Empty,
///             ),
///             mapper: NestedBracesMapper,
///         }.spec_parse(i)
///
/// );
///
/// ```
pub struct Fix<Body>(pub Body);

} // verus!
