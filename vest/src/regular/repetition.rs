use alloc::vec::Vec;

use crate::properties::*;

/// A repeated collection of values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepeatResult<T>(pub Vec<T>);

/// Repeat the inner combinator a fixed number of times.
pub struct RepeatN<C>(pub C, pub usize);

impl<C> RepeatN<C> {
    /// Create a fixed-count repeater.
    pub fn new(inner: C, count: usize) -> Self {
        Self(inner, count)
    }
}

impl<'x, I, O, C> Combinator<'x, I, O> for RepeatN<C>
where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<'x, I, O>,
    C::SType: Clone,
{
    type Type = RepeatResult<C::Type>;
    type SType = RepeatResult<C::SType>;

    fn length(&self, v: Self::SType) -> usize {
        if v.0.len() != self.1 {
            return 0;
        }
        v.0.iter().fold(0, |acc, item| acc + self.0.length(item.clone()))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let mut values = Vec::with_capacity(self.1);
        let mut consumed = 0usize;
        for _ in 0..self.1 {
            let (n, v) = self.0.parse(s.subrange(consumed, s.len()))?;
            if n == 0 {
                return Err(ParseError::Other("repeat element length was zero".into()));
            }
            consumed = consumed.saturating_add(n);
            values.push(v);
        }
        Ok((consumed, RepeatResult(values)))
    }

    fn serialize(
        &self,
        v: Self::SType,
        data: &mut O,
        mut pos: usize,
    ) -> Result<usize, SerializeError> {
        let start = pos;
        if v.0.len() != self.1 {
            return Err(SerializeError::Other("RepeatN length mismatch".into()));
        }

        for item in &v.0 {
            let n = self.0.serialize(item.clone(), data, pos)?;
            pos += n;
        }
        Ok(pos - start)
    }
}

/// Repeat the inner combinator until input is exhausted.
pub struct Repeat<C>(pub C);

impl<C> Repeat<C> {
    /// Create a repeater that consumes until input ends.
    pub fn new(inner: C) -> Self {
        Self(inner)
    }
}

impl<'x, I, O, C> Combinator<'x, I, O> for Repeat<C>
where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<'x, I, O>,
    C::SType: Clone,
{
    type Type = RepeatResult<C::Type>;
    type SType = RepeatResult<C::SType>;

    fn length(&self, v: Self::SType) -> usize {
        v.0.iter().fold(0, |acc, item| acc + self.0.length(item.clone()))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let mut values = Vec::new();
        let mut consumed = 0usize;
        while consumed < s.len() {
            let (n, v) = self.0.parse(s.subrange(consumed, s.len()))?;
            if n == 0 {
                return Err(ParseError::Other("repeat element length was zero".into()));
            }
            consumed = consumed.saturating_add(n);
            values.push(v);
        }
        Ok((consumed, RepeatResult(values)))
    }

    fn serialize(
        &self,
        v: Self::SType,
        data: &mut O,
        mut pos: usize,
    ) -> Result<usize, SerializeError> {
        let start = pos;
        for item in &v.0 {
            let n = self.0.serialize(item.clone(), data, pos)?;
            pos += n;
        }
        Ok(pos - start)
    }
}
