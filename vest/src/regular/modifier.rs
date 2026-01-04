use crate::properties::*;

use super::bytes::Variable;

/// Simple mapping trait used by `Mapped`.
pub trait Mapper<Src> {
    /// Output type produced by this mapper.
    type Dst;

    /// Convert from parsed value to mapped value.
    fn forward(&self, src: Src) -> Self::Dst;
    /// Convert from mapped value back to parsed value.
    fn backward(&self, dst: Self::Dst) -> Src;
}

/// Fallible mapping trait used by `TryMap`.
pub trait TryMapper<Src> {
    /// Output type produced by this mapper.
    type Dst;

    /// Convert from parsed value to mapped value.
    fn forward(&self, src: Src) -> Result<Self::Dst, ParseError>;
    /// Convert from mapped value back to parsed value.
    fn backward(&self, dst: Self::Dst) -> Result<Src, SerializeError>;
}

/// Predicate used by `Refined`.
pub trait Pred<Input> {
    /// Returns true when the input satisfies the predicate.
    fn apply(&self, input: &Input) -> bool;
}

/// Combinator that maps the parsed value using a reversible mapper.
pub struct Mapped<Inner, M> {
    /// The inner combinator to parse or serialize.
    pub inner: Inner,
    /// Mapping logic applied to the parsed value.
    pub mapper: M,
}

impl<'x, I, O, Inner, M, Src> Combinator<'x, I, O> for Mapped<Inner, M>
where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O, Type = Src, SType = Src>,
    M: Mapper<Src>,
    Src: Clone,
    M::Dst: Clone,
{
    type Type = M::Dst;
    type SType = M::Dst;

    fn length(&self, v: Self::SType) -> usize {
        let src = self.mapper.backward(v.clone());
        self.inner.length(src)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v) = self.inner.parse(s)?;
        Ok((n, self.mapper.forward(v)))
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        let src = self.mapper.backward(v);
        self.inner.serialize(src, data, pos)
    }
}

/// Combinator that maps the parsed value using fallible conversions.
pub struct TryMap<Inner, M> {
    /// The inner combinator to parse or serialize.
    pub inner: Inner,
    /// Fallible mapping logic applied to the parsed value.
    pub mapper: M,
}

impl<'x, I, O, Inner, M, Src> Combinator<'x, I, O> for TryMap<Inner, M>
where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O, Type = Src, SType = Src>,
    M: TryMapper<Src>,
    Src: Clone,
    M::Dst: Clone,
{
    type Type = M::Dst;
    type SType = M::Dst;

    fn length(&self, v: Self::SType) -> usize {
        match self.mapper.backward(v.clone()) {
            Ok(src) => self.inner.length(src),
            Err(_) => 0,
        }
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v) = self.inner.parse(s)?;
        let mapped = self.mapper.forward(v)?;
        Ok((n, mapped))
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        let src = self.mapper.backward(v)?;
        self.inner.serialize(src, data, pos)
    }
}

/// Combinator that refines the result of an `inner` combinator with a predicate.
pub struct Refined<Inner, P> {
    /// The combinator whose output will be checked.
    pub inner: Inner,
    /// Predicate that must accept the parsed value.
    pub predicate: P,
}

impl<'x, I, O, Inner, P> Combinator<'x, I, O> for Refined<Inner, P>
where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O>,
    P: Pred<Inner::Type>,
{
    type Type = Inner::Type;
    type SType = Inner::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.inner.length(v)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        match self.inner.parse(s) {
            Ok((n, v)) if self.predicate.apply(&v) => Ok((n, v)),
            Ok(_) => Err(ParseError::RefinedPredicateFailed),
            Err(e) => Err(e),
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        self.inner.serialize(v, data, pos)
    }
}

/// Combinator that runs its inner combinator only when `cond` is true.
pub struct Cond<Inner> {
    /// Whether the inner combinator is allowed to run.
    pub cond: bool,
    /// The conditional combinator.
    pub inner: Inner,
}

impl<'x, I, O, Inner> Combinator<'x, I, O> for Cond<Inner>
where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<'x, I, O>,
{
    type Type = Inner::Type;
    type SType = Inner::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.inner.length(v)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if self.cond {
            self.inner.parse(s)
        } else {
            Err(ParseError::CondFailed)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        if self.cond {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::Other("condition not satisfied".into()))
        }
    }
}

/// Combinator that chains a variable-length parser with a parser for its contents.
pub struct AndThen<Prev, Next>(pub Prev, pub Next);

impl<'x, I, O, Next> Combinator<'x, I, O> for AndThen<Variable, Next>
where
    I: VestInput + 'x,
    O: VestOutput<I>,
    Next: Combinator<'x, I, O>,
{
    type Type = Next::Type;
    type SType = Next::SType;

    fn length(&self, v: Self::SType) -> usize {
        self.0 .0.max(self.1.length(v))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, chunk) = <Variable as Combinator<'x, I, O>>::parse(&self.0, s)?;
        let (m, value) = self.1.parse(chunk)?;
        if m == n {
            Ok((n, value))
        } else {
            Err(ParseError::AndThenUnusedBytes)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        self.1.serialize(v, data, pos)
    }
}

/// Helper mapper that uses a pair of closures.
pub struct ClosureMapper<Src, Dst, F, G>
where
    F: Fn(Src) -> Dst,
    G: Fn(Dst) -> Src,
{
    /// Forward mapping closure.
    pub forward: F,
    /// Backward mapping closure.
    pub backward: G,
    /// Marker for the source type.
    pub _src: core::marker::PhantomData<Src>,
    /// Marker for the destination type.
    pub _dst: core::marker::PhantomData<Dst>,
}

impl<Src, Dst, F, G> Mapper<Src> for ClosureMapper<Src, Dst, F, G>
where
    F: Fn(Src) -> Dst,
    G: Fn(Dst) -> Src,
{
    type Dst = Dst;

    fn forward(&self, src: Src) -> Self::Dst {
        (self.forward)(src)
    }

    fn backward(&self, dst: Self::Dst) -> Src {
        (self.backward)(dst)
    }
}

/// Construct a [`ClosureMapper`].
pub fn closure_mapper<Src, Dst, F, G>(forward: F, backward: G) -> ClosureMapper<Src, Dst, F, G>
where
    F: Fn(Src) -> Dst,
    G: Fn(Dst) -> Src,
{
    ClosureMapper { forward, backward, _src: core::marker::PhantomData, _dst: core::marker::PhantomData }
}
