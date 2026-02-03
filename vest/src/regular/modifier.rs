use crate::properties::*;

use super::bytes::Variable;

/// Simple mapping trait used by `Mapped`.
pub trait Mapper {
    /// Input type consumed by this mapper.
    type Src<'p>;
    /// Output type produced by this mapper.
    type Dst<'p>;

    /// Borrowed version of the input type.
    type SrcBorrow<'s>;
    /// Borrowed version of the output type.
    type DstBorrow<'s>;

    /// Owned version of the input type.
    type SrcOwned;
    /// Owned version of the output type.
    type DstOwned;

    /// Convert from parsed value to mapped value.
    fn forward<'p>(&self, src: Self::Src<'p>) -> Self::Dst<'p>
    where
        Self::Dst<'p>: From<Self::Src<'p>>,
    {
        src.into()
    }
    /// Convert from mapped value back to parsed value.
    fn backward<'s>(&self, dst: Self::DstBorrow<'s>) -> Self::SrcBorrow<'s>
    where
        Self::SrcBorrow<'s>: From<Self::DstBorrow<'s>>,
    {
        dst.into()
    }
    /// Convert from generated owned value to mapped owned value.
    fn forward_owned(&self, src: Self::SrcOwned) -> Self::DstOwned
    where
        Self::DstOwned: From<Self::SrcOwned>,
    {
        src.into()
    }
}

/// Combinator that maps the parsed value using a reversible mapper.
pub struct Mapped<Inner, M> {
    /// The inner combinator to parse or serialize.
    pub inner: Inner,
    /// Mapping logic applied to the parsed value.
    pub mapper: M,
}

impl<Inner, M> Mapped<Inner, M> {
    /// Create a new `Mapped` combinator.
    pub fn new(inner: Inner, mapper: M) -> Self {
        Self { inner, mapper }
    }
}

impl<I, O, Inner, M> Combinator<I, O> for Mapped<Inner, M>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    for<'p, 's> M: Mapper<
        Src<'p> = Inner::Type<'p>,
        SrcBorrow<'s> = Inner::SType<'s>,
        SrcOwned = Inner::GType,
    >,
    for<'p> M::Dst<'p>: From<M::Src<'p>>,
    for<'s> M::SrcBorrow<'s>: From<M::DstBorrow<'s>>,
    M::DstOwned: From<M::SrcOwned>,
{
    type Type<'p>
        = M::Dst<'p>
    where
        I: 'p;
    type SType<'s>
        = M::DstBorrow<'s>
    where
        I: 's;
    type GType = M::DstOwned;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        let src: Inner::SType<'s> = self.mapper.backward(v).into();
        self.inner.length(src)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, v) = self.inner.parse(s)?;
        Ok((n, self.mapper.forward(v)))
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
        let src: Inner::SType<'s> = self.mapper.backward(v).into();
        self.inner.serialize(src, data, pos)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (n, v) = self.inner.generate(g)?;
        Ok((n, self.mapper.forward_owned(v)))
    }
}

/// Combinator that refines the result of an `inner` combinator with a predicate.
pub struct Refined<Inner, P> {
    /// The combinator whose output will be checked.
    pub inner: Inner,
    /// Predicate that must accept the parsed value.
    pub predicate: P,
}

impl<I, O, Inner, P> Combinator<I, O> for Refined<Inner, P>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    P: for<'s> Fn(Inner::SType<'s>) -> bool,
    for<'p, 's> Inner::SType<'s>: FromRef<'s, Inner::Type<'p>> + FromRef<'s, Inner::GType>,
{
    type Type<'p>
        = Inner::Type<'p>
    where
        I: 'p;
    type SType<'s>
        = Inner::SType<'s>
    where
        I: 's;
    type GType = Inner::GType;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.inner.length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        match self.inner.parse(s) {
            Ok((n, v)) if (self.predicate)(Inner::SType::ref_to_stype(&v)) => Ok((n, v)),
            Ok(_) => Err(ParseError::RefinedPredicateFailed),
            Err(e) => Err(e),
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
        self.inner.serialize(v, data, pos)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        loop {
            let (n, v) = self.inner.generate(g)?;
            if (self.predicate)(Inner::SType::ref_to_stype(&v)) {
                return Ok((n, v));
            }
        }
    }
}

/// Combinator that runs its inner combinator only when `lhs` equals `rhs`.
pub struct CondEq<T, Inner> {
    /// The left-hand side of the equality comparison.
    pub lhs: T,
    /// The right-hand side of the equality comparison.
    pub rhs: T,
    /// The conditional combinator.
    pub inner: Inner,
}

impl<I, O, T, Inner> Combinator<I, O> for CondEq<T, Inner>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    T: PartialEq,
{
    type Type<'p>
        = Inner::Type<'p>
    where
        I: 'p;
    type SType<'s>
        = Inner::SType<'s>
    where
        I: 's;
    type GType = Inner::GType;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.inner.length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        if self.lhs == self.rhs {
            self.inner.parse(s)
        } else {
            Err(ParseError::CondFailed)
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
        if self.lhs == self.rhs {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::Other("condition not satisfied".into()))
        }
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        if self.lhs == self.rhs {
            self.inner.generate(g)
        } else {
            Err(GenerateError::CondFailed)
        }
    }
}

/// Combinator that chains a variable-length parser with a parser for its contents.
pub struct AndThen<Prev, Next>(pub Prev, pub Next);

impl<I, O, Next> Combinator<I, O> for AndThen<Variable, Next>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Next: Combinator<I, O>,
{
    type Type<'p>
        = Next::Type<'p>
    where
        I: 'p;
    type SType<'s>
        = Next::SType<'s>
    where
        I: 's;
    type GType = Next::GType;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.0 .0
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, chunk) = <Variable as Combinator<I, O>>::parse(&self.0, s)?;
        let (m, value) = self.1.parse(&chunk)?;
        if m == n {
            Ok((n, value))
        } else {
            Err(ParseError::AndThenUnusedBytes)
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
        self.1.serialize(v, data, pos)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        self.1.generate(g)
    }
}

/// Combinator that makes sure `Inner` parses/serializes exactly `n` bytes.
pub struct FixedLen<Inner>(pub usize, pub Inner);

impl<I, O, Inner> Combinator<I, O> for FixedLen<Inner>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
{
    type Type<'p>
        = Inner::Type<'p>
    where
        I: 'p;
    type SType<'s>
        = Inner::SType<'s>
    where
        I: 's;
    type GType = Inner::GType;

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
        let (n, chunk) = <_ as Combinator<I, O>>::parse(&Variable(self.0), s)?;
        let (m, value) = self.1.parse(&chunk)?;
        if m == n {
            Ok((n, value))
        } else {
            Err(ParseError::AndThenUnusedBytes)
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
        self.1.serialize(v, data, pos)
    }

    fn generate(&self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        self.1.generate(g)
    }
}
