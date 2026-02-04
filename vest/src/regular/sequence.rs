use crate::properties::*;

/// Helper trait for the dependent second combinator in [`Pair`].
pub trait DepCombinator<In, I, O>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    In: Combinator<I, O>,
{
    /// The dependent combinator type for parsing/serialization.
    type Out: Combinator<I, O>;
    /// The dependent combinator type for generation.
    type OutGen<'a>: Combinator<I, O, GType = <Self::Out as Combinator<I, O>>::GType>;

    /// Build the dependent combinator for parsing/serialization.
    fn dep_snd<'a>(&self, fst: In::SType<'a>) -> Self::Out;
    /// Build the dependent combinator for generation.
    fn dep_snd_gen<'a>(&self, fst: &'a mut In::GType) -> Self::OutGen<'a>;
}

/// Dependent pair combinator where the second combinator depends on the result
/// of the first (monadic sequencing).
pub struct Pair<Fst, Dep> {
    pub fst: Fst,
    pub snd: Dep,
}

impl<Fst, Dep> Pair<Fst, Dep> {
    /// Create a new dependent pair combinator.
    pub fn new(fst: Fst, snd: Dep) -> Self {
        Self { fst, snd }
    }
}

impl<I, O, Fst, Dep> Combinator<I, O> for Pair<Fst, Dep>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Dep: DepCombinator<Fst, I, O>,
    for<'p, 's> Fst::SType<'s>: FromRef<'s, Fst::Type<'p>> + Copy,
{
    type Type<'p>
        = (Fst::Type<'p>, <Dep::Out as Combinator<I, O>>::Type<'p>)
    where
        I: 'p;
    type SType<'s>
        = (Fst::SType<'s>, <Dep::Out as Combinator<I, O>>::SType<'s>)
    where
        I: 's;
    type GType = (Fst::GType, <Dep::Out as Combinator<I, O>>::GType);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.fst.length(v.0) + self.snd.dep_snd(v.0).length(v.1)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, v1) = self.fst.parse(s)?;
        let dep_snd = self.snd.dep_snd(Fst::SType::ref_to_stype(&v1));
        let rest = s.skip(n);
        let (m, v2) = dep_snd.parse(&rest)?;
        Ok((n + m, (v1, v2)))
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
        let n = self.fst.serialize(v.0, data, pos)?;
        let dep_snd = self.snd.dep_snd(v.0);
        let m = dep_snd.serialize(v.1, data, pos + n)?;
        Ok(n + m)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (g1, mut v1) = self.fst.generate(g)?;
        let (g2, v2) = {
            let mut dep_snd = self.snd.dep_snd_gen(&mut v1);
            dep_snd.generate(g)?
        };
        Ok((g1 + g2, (v1, v2)))
    }
}

/// Tuple for sequencing.
impl<I, O, Fst, Snd> Combinator<I, O> for (Fst, Snd)
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p>
        = (Fst::Type<'p>, Snd::Type<'p>)
    where
        I: 'p;
    type SType<'s>
        = (Fst::SType<'s>, Snd::SType<'s>)
    where
        I: 's;
    type GType = (Fst::GType, Snd::GType);

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.0.length(v.0) + self.1.length(v.1)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, v1) = self.0.parse(s)?;
        let rest = s.skip(n);
        let (m, v2) = self.1.parse(&rest)?;
        Ok((n + m, (v1, v2)))
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
        let n = self.0.serialize(v.0, data, pos)?;
        let m = self.1.serialize(v.1, data, pos + n)?;
        Ok(n + m)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (g1, v1) = self.0.generate(g)?;
        let (g2, v2) = self.1.generate(g)?;
        Ok((g1 + g2, (v1, v2)))
    }
}

/// Marker trait for combinators whose parse result type is always `()`.
///
/// This is used to enable combinators like `Preceded` and `Terminated` to
/// work with unit-producing combinators without requiring complex higher-ranked
/// trait bounds.
pub trait UnitCombinator<I: VestInput + ?Sized, O: VestOutput<I>>: Combinator<I, O> {
    /// Parse the input and return the number of bytes consumed.
    fn parse_unit<'p>(&self, s: &'p I) -> Result<usize, ParseError>
    where
        I: 'p;
    /// Serialize the unit value.
    fn serialize_unit<'s>(&self, data: &mut O, pos: usize) -> Result<usize, SerializeError>
    where
        I: 's;
    /// Length of the serialized unit value.
    fn length_unit(&self) -> usize;
}

/// Apply `Fst` then `Snd`, returning only `Snd`'s result.
pub struct Preceded<Fst, Snd>(pub Fst, pub Snd);

impl<I, O, Fst, Snd> Combinator<I, O> for Preceded<Fst, Snd>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: UnitCombinator<I, O>,
    Snd: Combinator<I, O>,
{
    type Type<'p>
        = Snd::Type<'p>
    where
        I: 'p;
    type SType<'s>
        = Snd::SType<'s>
    where
        I: 's;
    type GType = Snd::GType;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.0.length_unit() + self.1.length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let n = self.0.parse_unit(s)?;
        let rest = s.skip(n);
        let (m, v) = self.1.parse(&rest)?;
        Ok((n + m, v))
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
        let n = self.0.serialize_unit(data, pos)?;
        let m = self.1.serialize(v, data, pos + n)?;
        Ok(n + m)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (g2, v2) = self.1.generate(g)?;
        Ok((g2, v2))
    }
}

pub struct Terminated<Fst, Snd>(pub Fst, pub Snd);

impl<I, O, Fst, Snd> Combinator<I, O> for Terminated<Fst, Snd>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: UnitCombinator<I, O>,
{
    type Type<'p>
        = Fst::Type<'p>
    where
        I: 'p;
    type SType<'s>
        = Fst::SType<'s>
    where
        I: 's;
    type GType = Fst::GType;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.0.length(v) + self.1.length_unit()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, v) = self.0.parse(s)?;
        let rest = s.skip(n);
        let m = self.1.parse_unit(&rest)?;
        Ok((n + m, v))
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
        let n = self.0.serialize(v, data, pos)?;
        let m = self.1.serialize_unit(data, pos + n)?;
        Ok(n + m)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (g1, v1) = self.0.generate(g)?;
        Ok((g1, v1))
    }
}
