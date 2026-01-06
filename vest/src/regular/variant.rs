use crate::properties::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

/// Try the first parser, fall back to the second on error.
pub struct Choice<Fst, Snd>(pub Fst, pub Snd);

impl<Fst, Snd> Choice<Fst, Snd> {
    pub fn new(fst: Fst, snd: Snd) -> Self {
        Self(fst, snd)
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for Choice<Fst, Snd>
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p> = Either<Fst::Type<'p>, Snd::Type<'p>>;
    type SType<'s> = Either<Fst::SType<'s>, Snd::SType<'s>>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        match v {
            Either::Left(v) => self.0.length(v),
            Either::Right(v) => self.1.length(v),
        }
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
        if let Ok((n, v)) = self.0.parse(s.clone()) {
            Ok((n, Either::Left(v)))
        } else {
            let (n, v) = self.1.parse(s)?;
            Ok((n, Either::Right(v)))
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        match v {
            Either::Left(v) => self.0.serialize(v, data, pos),
            Either::Right(v) => self.1.serialize(v, data, pos),
        }
    }
}

/// Optional combinator that never fails; consumes zero bytes on `None`.
pub struct Opt<T>(pub T);

impl<T> Opt<T> {
    pub fn new(inner: T) -> Self {
        Self(inner)
    }
}

impl<I, O, T> Combinator<I, O> for Opt<T>
where
    I: VestInput,
    O: VestOutput<I>,
    T: Combinator<I, O>,
{
    type Type<'p> = Option<T::Type<'p>>;
    type SType<'s> = Option<T::SType<'s>>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        match v {
            Some(v) => self.0.length(v),
            None => 0,
        }
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
        if let Ok((n, v)) = self.0.parse(s) {
            Ok((n, Some(v)))
        } else {
            Ok((0, None))
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        match v {
            Some(v) => self.0.serialize(v, data, pos),
            None => {
                if pos <= data.len() {
                    Ok(0)
                } else {
                    Err(SerializeError::InsufficientBuffer)
                }
            }
        }
    }
}

/// Parse an optional prefix followed by a required tail.
pub struct OptThen<Fst, Snd>(pub Opt<Fst>, pub Snd);

impl<Fst, Snd> OptThen<Fst, Snd> {
    pub fn new(fst: Fst, snd: Snd) -> Self {
        Self(Opt(fst), snd)
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for OptThen<Fst, Snd>
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p> = (Option<Fst::Type<'p>>, Snd::Type<'p>);
    type SType<'s> = (Option<Fst::SType<'s>>, Snd::SType<'s>);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        let fst_len = v.0.map(|val| self.0 .0.length(val)).unwrap_or(0);
        fst_len + self.1.length(v.1)
    }

    fn parse<'p>(&self, s: I) -> Result<(usize, Self::Type<'p>), ParseError> {
        if let Ok((n0, v0)) = self.0 .0.parse(s.clone()) {
            let (n1, v1) = self.1.parse(s.subrange(n0, s.len()))?;
            Ok((n0 + n1, (Some(v0), v1)))
        } else {
            let (n1, v1) = self.1.parse(s)?;
            Ok((n1, (None, v1)))
        }
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let mut written = 0;
        if let Some(v0) = v.0 {
            written = self.0 .0.serialize(v0, data, pos)?;
        }
        let n1 = self.1.serialize(v.1, data, pos + written)?;
        Ok(written + n1)
    }
}
