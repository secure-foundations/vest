use crate::properties::*;

/// Combinator that always succeeds and consumes nothing.
pub struct Success;

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<'x, I, O> for Success {
    type Type = ();
    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    fn parse(&self, _s: I) -> Result<(usize, Self::Type), ParseError> {
        Ok((0, ()))
    }

    fn serialize(&self, _v: Self::SType, _data: &mut O, _pos: usize) -> Result<usize, SerializeError> {
        Ok(0)
    }
}
