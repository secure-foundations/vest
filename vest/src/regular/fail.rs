use alloc::string::String;

use crate::properties::*;

/// Combinator that always fails with a custom error message.
pub struct Fail(pub String);

impl<'x, I: VestInput + ?Sized, O: VestOutput<I>> Combinator<I, O> for Fail {
    type Type<'p>
        = ()
    where
        I: 'p;
    type SType<'s>
        = ()
    where
        I: 's;
    type GType = ();

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        0
    }

    fn parse<'p>(&self, _s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        Err(ParseError::Other(self.0.clone()))
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
        Err(SerializeError::Other(self.0.clone()))
    }

    fn generate(&self, _g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        Err(GenerateError::Other(self.0.clone()))
    }
}
