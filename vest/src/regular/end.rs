use crate::properties::*;

/// Combinator that succeeds only at the end of the input buffer and consumes nothing.
pub struct End;

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<'x, I, O> for End {
    type Type = ();
    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if s.len() == 0 {
            Ok((0, ()))
        } else {
            Err(ParseError::NotEof)
        }
    }

    fn serialize(&self, _v: Self::SType, _data: &mut O, _pos: usize) -> Result<usize, SerializeError> {
        Ok(0)
    }
}
