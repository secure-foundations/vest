use crate::properties::*;

/// Combinator that succeeds only at the end of the input buffer and consumes nothing.
pub struct End;

impl<'x, I: VestInput + ?Sized, O: VestOutput<I>> Combinator<I, O> for End {
    type Type<'p>
        = ()
    where
        I: 'p;
    type SType<'s>
        = ()
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        0
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
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
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        Ok(0)
    }
}
