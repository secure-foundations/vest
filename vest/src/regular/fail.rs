use alloc::string::String;

use crate::properties::*;

/// Combinator that always fails with a custom error message.
pub struct Fail(pub String);

impl<'x, I: VestInput, O: VestOutput<I>> Combinator<'x, I, O> for Fail {
    type Type = ();
    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        0
    }

    fn parse(&self, _s: I) -> Result<(usize, Self::Type), ParseError> {
        Err(ParseError::Other(self.0.clone()))
    }

    fn serialize(&self, _v: Self::SType, _data: &mut O, _pos: usize) -> Result<usize, SerializeError> {
        Err(SerializeError::Other(self.0.clone()))
    }
}
