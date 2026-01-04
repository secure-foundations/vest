use crate::properties::*;

/// Sequentially apply two combinators and return both results.
pub struct Pair<Fst, Snd> {
    pub fst: Fst,
    pub snd: Snd,
}

impl<Fst, Snd> Pair<Fst, Snd> {
    pub fn new(fst: Fst, snd: Snd) -> Self {
        Self { fst, snd }
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for Pair<Fst, Snd>
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type = (Fst::Type, Snd::Type);
    type SType<'s> = (Fst::SType<'s>, Snd::SType<'s>);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        self.fst.length(v.0) + self.snd.length(v.1)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v1) = self.fst.parse(s.clone())?;
        let (m, v2) = self.snd.parse(s.subrange(n, s.len()))?;
        Ok((n + m, (v1, v2)))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let n = self.fst.serialize(v.0, data, pos)?;
        let m = self.snd.serialize(v.1, data, pos + n)?;
        Ok(n + m)
    }
}

/// Tuple sequencing convenience.
impl<I, O, Fst, Snd> Combinator<I, O> for (Fst, Snd)
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type = (Fst::Type, Snd::Type);
    type SType<'s> = (Fst::SType<'s>, Snd::SType<'s>);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        Pair::new(&self.0, &self.1).length(v)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        Pair::new(&self.0, &self.1).parse(s)
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        Pair::new(&self.0, &self.1).serialize(v, data, pos)
    }
}

/// Apply `Fst` then `Snd`, returning only `Snd`'s result.
pub struct Preceded<Fst, Snd>(pub Fst, pub Snd);

impl<I, O, Fst, Snd> Combinator<I, O> for Preceded<Fst, Snd>
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O, Type = ()>,
    Snd: Combinator<I, O>,
    for<'s> Fst::SType<'s>: From<()>,
{
    type Type = Snd::Type;
    type SType<'s> = Snd::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        let prefix: Fst::SType<'s> = ().into();
        Pair::new(&self.0, &self.1).length((prefix, v))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, _) = self.0.parse(s.clone())?;
        let (m, v) = self.1.parse(s.subrange(n, s.len()))?;
        Ok((n + m, v))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let n = self.0.serialize(().into(), data, pos)?;
        let m = self.1.serialize(v, data, pos + n)?;
        Ok(n + m)
    }
}

/// Apply `Fst` then `Snd`, returning only `Fst`'s result.
pub struct Terminated<Fst, Snd>(pub Fst, pub Snd);

impl<I, O, Fst, Snd> Combinator<I, O> for Terminated<Fst, Snd>
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O, Type = ()>,
    for<'s> Snd::SType<'s>: From<()>,
{
    type Type = Fst::Type;
    type SType<'s> = Fst::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        Pair::new(&self.0, &self.1).length((v, ().into()))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v) = self.0.parse(s.clone())?;
        let (m, _) = self.1.parse(s.subrange(n, s.len()))?;
        Ok((n + m, v))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let n = self.0.serialize(v, data, pos)?;
        let m = self.1.serialize(().into(), data, pos + n)?;
        Ok(n + m)
    }
}
