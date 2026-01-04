use crate::properties::*;

use super::modifier::AndThen;

/// Combinator for parsing and serializing a fixed number of bytes (dynamically known).
#[derive(Copy, Debug, PartialEq, Eq)]
pub struct Variable(pub usize);

impl Variable {
    /// Chains this combinator with another combinator, enforcing that the chained parser consumes
    /// exactly the number of bytes selected by `Variable`.
    pub fn and_then<'x, I, O, Next>(self, next: Next) -> AndThen<Variable, Next>
    where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
        Next: Combinator<'x, I, O>,
    {
        AndThen(self, next)
    }
}

impl<'x, I, O> Combinator<'x, I, O> for Variable
where
    I: VestInput + 'x,
    O: VestOutput<I>,
{
    type Type = I;
    type SType = I;

    fn length(&self, _v: Self::SType) -> usize {
        self.0
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if self.0 <= s.len() {
            Ok((self.0, s.subrange(0, self.0)))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
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

impl<'x, const N: usize, I, O> Combinator<'x, I, O> for Fixed<N>
where
    I: VestInput + 'x,
    O: VestOutput<I>,
{
    type Type = I;
    type SType = I;

    fn length(&self, _v: Self::SType) -> usize {
        N
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if N <= s.len() {
            Ok((N, s.subrange(0, N)))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
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

impl<'x, I: VestInput + 'x, O: VestOutput<I>> Combinator<'x, I, O> for Tail {
    type Type = I;
    type SType = I;

    fn length(&self, v: Self::SType) -> usize {
        v.len()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        Ok((s.len(), s))
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        if v.len() <= data.len().saturating_sub(pos) {
            data.set_range(pos, &v);
            Ok(v.len())
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}
