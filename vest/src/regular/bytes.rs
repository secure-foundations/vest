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
        I: VestPublicInput,
        O: VestPublicOutput<I>,
        Next: Combinator<I, O>,
    {
        AndThen(self, next)
    }
}

impl<I, O> Combinator<I, O> for Variable
where
    I: VestInput,
    O: VestOutput<I>,
{
    type Type = I;
    type SType<'s> = I;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize {
        self.0
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if self.0 <= s.len() {
            Ok((self.0, s.subrange(0, self.0)))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
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
    I: VestInput,
    O: VestOutput<I>,
{
    type Type = I;
    type SType<'s> = I;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize {
        N
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if N <= s.len() {
            Ok((N, s.subrange(0, N)))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
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

impl<'x, I: VestInput + 'x, O: VestOutput<I>> Combinator<I, O> for Tail {
    type Type = I;
    type SType<'s> = I;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        v.len()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        Ok((s.len(), s))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        if v.len() <= data.len().saturating_sub(pos) {
            data.set_range(pos, &v);
            Ok(v.len())
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}
