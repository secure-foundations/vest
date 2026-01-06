use crate::properties::*;

use super::modifier::AndThen;

/// Combinator for parsing and serializing a fixed number of bytes (dynamically known).
#[derive(Copy, Debug, PartialEq, Eq)]
pub struct Variable(pub usize);

impl Variable {
    /// Chains this combinator with another combinator, enforcing that the chained parser consumes
    /// exactly the number of bytes selected by `Variable`.
    pub fn and_then<I, O, Next>(self, next: Next) -> AndThen<Variable, Next>
    where
        I: VestPublicInput + ?Sized,
        O: VestPublicOutput<I>,
        Next: Combinator<I, O>,
    {
        AndThen(self, next)
    }
}

impl<I, O> Combinator<I, O> for Variable
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
{
    type Type<'p>
        = &'p I
    where
        I: 'p;
    type SType<'s>
        = &'s I
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.0
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if self.0 <= s.len() {
            Ok((self.0, s.take(self.0)))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        if v.len() <= data.len() && pos <= data.len().saturating_sub(v.len()) {
            data.set_range(pos, &v);
            Ok(self.0)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

/// Combinator for parsing and serializing a fixed number of bytes (statically known).
#[derive(Copy, Debug, PartialEq, Eq)]
pub struct Fixed<const N: usize>;

impl<const N: usize, I, O> Combinator<I, O> for Fixed<N>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
{
    type Type<'p>
        = &'p I
    where
        I: 'p;
    type SType<'s>
        = &'s I
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        N
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if N <= s.len() {
            Ok((N, s.take(N)))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        if v.len() <= data.len().saturating_sub(pos) {
            data.set_range(pos, &v);
            Ok(N)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

/// Combinator that returns the rest of the input bytes from the current position.
#[derive(Copy, Debug, PartialEq, Eq)]
pub struct Tail;

impl<I: VestInput + ?Sized, O: VestOutput<I>> Combinator<I, O> for Tail {
    type Type<'p>
        = &'p I
    where
        I: 'p;
    type SType<'s>
        = &'s I
    where
        I: 's;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        v.len()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        Ok((s.len(), s))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        if v.len() <= data.len().saturating_sub(pos) {
            data.set_range(pos, &v);
            Ok(v.len())
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}
