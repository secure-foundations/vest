use alloc::string::String;

use crate::properties::*;

/// Combinator that always fails with a custom error message.
pub struct Fail(pub String);

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<I, O> for Fail {
    type Type = ();
    type SType<'s> = ();

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize {
        0
    }

    fn parse(&self, _s: I) -> Result<(usize, Self::Type), ParseError> {
        Err(ParseError::Other(self.0.clone()))
    }

    fn serialize<'s>(
        &self,
        _v: Self::SType<'s>,
        _data: &mut O,
        _pos: usize,
    ) -> Result<usize, SerializeError> {
        Err(SerializeError::Other(self.0.clone()))
    }
}
