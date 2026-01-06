use rand::Rng;

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
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p>
        = Either<Fst::Type<'p>, Snd::Type<'p>>
    where
        I: 'p;
    type SType<'s>
        = Either<Fst::SType<'s>, Snd::SType<'s>>
    where
        I: 's;
    type GType = Either<Fst::GType, Snd::GType>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match v {
            Either::Left(v) => self.0.length(v),
            Either::Right(v) => self.1.length(v),
        }
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if let Ok((n, v)) = self.0.parse(s) {
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
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        match v {
            Either::Left(v) => self.0.serialize(v, data, pos),
            Either::Right(v) => self.1.serialize(v, data, pos),
        }
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        if g.rng.random_bool(0.5) {
            let (n, v) = self.0.generate(g)?;
            Ok((n, Either::Left(v)))
        } else {
            let (n, v) = self.1.generate(g)?;
            Ok((n, Either::Right(v)))
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
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    T: Combinator<I, O>,
{
    type Type<'p>
        = Option<T::Type<'p>>
    where
        I: 'p;
    type SType<'s>
        = Option<T::SType<'s>>
    where
        I: 's;
    type GType = Option<T::GType>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match v {
            Some(v) => self.0.length(v),
            None => 0,
        }
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
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
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
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

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        if g.rng.random_bool(0.5) {
            let (n, v) = self.0.generate(g)?;
            Ok((n, Some(v)))
        } else {
            Ok((0, None))
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
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p>
        = (Option<Fst::Type<'p>>, Snd::Type<'p>)
    where
        I: 'p;
    type SType<'s>
        = (Option<Fst::SType<'s>>, Snd::SType<'s>)
    where
        I: 's;
    type GType = (Option<Fst::GType>, Snd::GType);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        let fst_len = v.0.map(|val| self.0 .0.length(val)).unwrap_or(0);
        fst_len + self.1.length(v.1)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if let Ok((n0, v0)) = self.0 .0.parse(s) {
            let rest = s.skip(n0);
            let (n1, v1) = self.1.parse(&rest)?;
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
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        let mut written = 0;
        if let Some(v0) = v.0 {
            written = self.0 .0.serialize(v0, data, pos)?;
        }
        let n1 = self.1.serialize(v.1, data, pos + written)?;
        Ok(written + n1)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (n1, v1) = self.1.generate(g)?;
        if g.rng.random_bool(0.5) {
            let (n0, v0) = self.0 .0.generate(g)?;
            Ok((n0 + n1, (Some(v0), v1)))
        } else {
            Ok((n1, (None, v1)))
        }
    }
}
