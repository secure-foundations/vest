use crate::properties::*;

/// Combinator that always succeeds and consumes nothing.
pub struct Success;

impl<'x, I: VestInput + ?Sized, O: VestOutput<I>> Combinator<I, O> for Success {
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
        Ok((0, ()))
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

    fn generate(&self, _g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        Ok((0, ()))
    }
}
