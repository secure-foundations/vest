use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Infallible serialization for any [`Combinator`] when the buffer is large enough.
///
/// Returns the number of bytes written. Guaranteed to succeed because the
/// precondition requires the buffer to have sufficient space, and the
/// strengthened [`Combinator::serialize`] ensures that `Err` can only occur
/// when the buffer is too small — a contradiction with the precondition.
pub fn serialize_infallible<'x, I, O, C>(
    combinator: &C,
    v: C::SType,
    buf: &mut O,
    pos: usize,
) -> (n: usize)
    where
        I: VestInput,
        O: VestOutput<I>,
        C: Combinator<'x, I, O>,
        C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
    requires
        combinator@.requires(),
        combinator.ex_requires(),
        combinator@.wf(v@),
        combinator@.spec_serialize(v@).len() <= usize::MAX,
        pos + combinator@.spec_serialize(v@).len() <= old(buf)@.len() <= usize::MAX,
    ensures
        buf@.len() == old(buf)@.len(),
        pos <= usize::MAX - n && pos + n <= buf@.len(),
        n == combinator@.spec_serialize(v@).len(),
        buf@ == seq_splice(old(buf)@, pos, combinator@.spec_serialize(v@)),
{
    match combinator.serialize(v, buf, pos) {
        Ok(n) => n,
        Err(_) => {
            proof { assert(false); }
            0
        }
    }
}

} // verus!
