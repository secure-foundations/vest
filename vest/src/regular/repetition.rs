use alloc::vec::Vec;

use crate::properties::*;

/// Repeat the inner combinator a fixed number of times.
pub struct RepeatN<C>(pub C, pub usize);

impl<C> RepeatN<C> {
    /// Create a fixed-count repeater.
    pub fn new(inner: C, count: usize) -> Self {
        Self(inner, count)
    }
}

impl<I, O, C> Combinator<I, O> for RepeatN<C>
where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<I, O>,
    for<'s> C::SType<'s>: 's + Copy,
{
    type Type<'p> = Vec<C::Type<'p>>;
    type SType<'s> = &'s [C::SType<'s>];

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        if v.len() != self.1 {
            return 0;
        }
        v.iter().fold(0, |acc, item| acc + self.0.length(*item))
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
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
        Ok((consumed, values))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        mut pos: usize,
    ) -> Result<usize, SerializeError> {
        let start = pos;
        if v.len() != self.1 {
            return Err(SerializeError::Other("RepeatN length mismatch".into()));
        }

        for item in v {
            let n = self.0.serialize(*item, data, pos)?;
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

impl<I, O, C> Combinator<I, O> for Repeat<C>
where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<I, O>,
    for<'s> C::SType<'s>: 's + Copy,
{
    type Type<'p> = Vec<C::Type<'p>>;
    type SType<'s> = &'s [C::SType<'s>];

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        v.iter().fold(0, |acc, item| acc + self.0.length(*item))
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
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
        Ok((consumed, values))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        mut pos: usize,
    ) -> Result<usize, SerializeError> {
        let start = pos;
        for item in v {
            let n = self.0.serialize(*item, data, pos)?;
            pos += n;
        }
        Ok(pos - start)
    }
}
