use crate::properties::*;

/// Combinator that always succeeds and consumes nothing.
pub struct Success;

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<I, O> for Success {
    type Type = ();
    type SType<'s> = ();

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize {
        0
    }

    fn parse(&self, _s: I) -> Result<(usize, Self::Type), ParseError> {
        Ok((0, ()))
    }

    fn serialize<'s>(
        &self,
        _v: Self::SType<'s>,
        _data: &mut O,
        _pos: usize,
    ) -> Result<usize, SerializeError> {
        Ok(0)
    }
}
