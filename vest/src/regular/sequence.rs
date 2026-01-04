use crate::properties::*;


/// Dependent pair combinator where the second combinator depends on the result
/// of the first (sequentially).
pub struct Pair<Fst, Snd, DepSnd> {
    pub fst: Fst,
    _snd: core::marker::PhantomData<Snd>,
    pub dep_snd: DepSnd,
}

impl<Fst, Snd, DepSnd> Pair<Fst, Snd, DepSnd> {
    /// Create a new dependent pair combinator.
    pub fn new(fst: Fst, dep_snd: DepSnd) -> Self {
        Self {
            fst,
            _snd: core::marker::PhantomData,
            dep_snd,
        }
    }
}

impl<I, O, Fst, Snd, DepSnd> Combinator<I, O> for Pair<Fst, Snd, DepSnd>
where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    DepSnd: for<'s> Fn(Fst::SType<'s>) -> Snd,
    for<'s> Fst::SType<'s>: From<&'s Fst::Type> + Copy,
{
    type Type = (Fst::Type, Snd::Type);
    type SType<'s> = (Fst::SType<'s>, Snd::SType<'s>);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        self.fst.length(v.0)
            + (self.dep_snd)(v.0).length(v.1)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v1) = self.fst.parse(s.clone())?;
        let dep_snd = (self.dep_snd)((&v1).into());
        let (m, v2) = dep_snd.parse(s.subrange(n, s.len()))?;
        Ok((n + m, (v1, v2)))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let n = self.fst.serialize(v.0, data, pos)?;
        let dep_snd = (self.dep_snd)(v.0);
        let m = dep_snd.serialize(v.1, data, pos + n)?;
        Ok(n + m)
    }
}

/// Tuple for sequencing.
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
        self.0.length(v.0) + self.1.length(v.1)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v1) = self.0.parse(s.clone())?;
        let (m, v2) = self.1.parse(s.subrange(n, s.len()))?;
        Ok((n + m, (v1, v2)))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let n = self.0.serialize(v.0, data, pos)?;
        let m = self.1.serialize(v.1, data, pos + n)?;
        Ok(n + m)
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
        (&self.0, &self.1).length((prefix, v))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (nm, (_, v)) = (&self.0, &self.1).parse(s)?;
        Ok((nm, v))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        (&self.0, &self.1).serialize((().into(), v), data, pos)
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
        let suffix: Snd::SType<'s> = ().into();
        (&self.0, &self.1).length((v, suffix))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (nm, (v, _)) = (&self.0, &self.1).parse(s)?;
        Ok((nm, v))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        (&self.0, &self.1).serialize((v, ().into()), data, pos)
    }
}
