use crate::properties::*;

/// Combinator that succeeds only at the end of the input buffer and consumes nothing.
pub struct End;

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<I, O> for End {
    type Type = ();
    type SType<'s> = ();

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize {
        0
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if s.len() == 0 {
            Ok((0, ()))
        } else {
            Err(ParseError::NotEof)
        }
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
