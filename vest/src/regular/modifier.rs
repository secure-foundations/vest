use crate::{properties::*, regular::sequence::FromRef};

use super::bytes::Variable;

// /// Combinator that maps the parsed value using a reversible mapper.
// pub struct Mapped<Inner, Dst, RefDst> {
//     /// The inner combinator to parse or serialize.
//     pub inner: Inner,
//     _dst: core::marker::PhantomData<Dst>,
//     _ref_dst: core::marker::PhantomData<RefDst>,
// }

// impl<Inner, Dst, RefDst> Mapped<Inner, Dst, RefDst> {
//     /// Create a new `Mapped` combinator.
//     pub fn new(inner: Inner) -> Self {
//         Self {
//             inner,
//             _dst: core::marker::PhantomData,
//             _ref_dst: core::marker::PhantomData,
//         }
//     }
// }

// impl<I, O, Inner, Dst, RefDst> Combinator<I, O> for Mapped<Inner, Dst, RefDst>
// where
//     I: VestInput,
//     O: VestOutput<I>,
//     Inner: Combinator<I, O>,
//     Dst: From<Inner::Type>,
//     for<'s> Inner::SType<'s>: From<RefDst>,
// {
//     type Type = Dst;
//     type SType<'s> = RefDst;

//     fn length<'s>(&self, v: Self::SType<'s>) -> usize {
//         let src: Inner::SType<'s> = v.into();
//         self.inner.length(src)
//     }

//     fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
//         let (n, v) = self.inner.parse(s)?;
//         Ok((n, v.into()))
//     }

//     fn serialize<'s>(
//         &self,
//         v: Self::SType<'s>,
//         data: &mut O,
//         pos: usize,
//     ) -> Result<usize, SerializeError> {
//         let src: Inner::SType<'s> = v.into();
//         self.inner.serialize(src, data, pos)
//     }
// }

/// Simple mapping trait used by `Mapped`.
pub trait Mapper {
    /// Input type consumed by this mapper.
    type Src;
    /// Output type produced by this mapper.
    type Dst;

    /// Borrowed version of the input type.
    type SrcBorrow<'s>;
    /// Borrowed version of the output type.
    type DstBorrow<'s>;

    /// Convert from parsed value to mapped value.
    fn forward(&self, src: Self::Src) -> Self::Dst
    where
        Self::Dst: From<Self::Src>,
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
}

// /// Fallible mapping trait used by `TryMap`.
// pub trait TryMapper<Src> {
//     /// Output type produced by this mapper.
//     type Dst;

//     /// Convert from parsed value to mapped value.
//     fn forward(&self, src: Src) -> Result<Self::Dst, ParseError>;
//     /// Convert from mapped value back to parsed value.
//     fn backward(&self, dst: Self::Dst) -> Result<Src, SerializeError>;
// }

// /// Predicate used by `Refined`.
// pub trait Pred<Input> {
//     /// Returns true when the input satisfies the predicate.
//     fn apply(&self, input: &Input) -> bool;
// }

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
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    for<'s> M: Mapper<Src = Inner::Type, SrcBorrow<'s> = Inner::SType<'s>>,
    M::Dst: From<M::Src>,
    for<'s> M::SrcBorrow<'s>: From<M::DstBorrow<'s>>,
{
    type Type = M::Dst;
    type SType<'s> = M::DstBorrow<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        let src: Inner::SType<'s> = self.mapper.backward(v).into();
        self.inner.length(src)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v) = self.inner.parse(s)?;
        Ok((n, self.mapper.forward(v)))
    }

    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError> {
        let src: Inner::SType<'s> = self.mapper.backward(v).into();
        self.inner.serialize(src, data, pos)
    }
}

// /// Combinator that maps the parsed value using fallible conversions.
// pub struct TryMap<Inner, M> {
//     /// The inner combinator to parse or serialize.
//     pub inner: Inner,
//     /// Fallible mapping logic applied to the parsed value.
//     pub mapper: M,
// }

// impl<I, O, Inner, M, Src> Combinator<I, O> for TryMap<Inner, M>
// where
//     I: VestInput,
//     O: VestOutput<I>,
//     Inner: Combinator<I, O, Type = Src>,
//     M: TryMapper<Src>,
//     Src: Clone,
//     M::Dst: Clone,
//     for<'s> Inner::SType<'s>: From<Src>,
// {
//     type Type = M::Dst;
//     type SType<'s> = M::Dst;

//     fn length<'s>(&self, v: Self::SType<'s>) -> usize {
//         match self.mapper.backward(v.clone()) {
//             Ok(src) => self.inner.length(src.into()),
//             Err(_) => 0,
//         }
//     }

//     fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
//         let (n, v) = self.inner.parse(s)?;
//         let mapped = self.mapper.forward(v)?;
//         Ok((n, mapped))
//     }

//     fn serialize<'s>(
//         &self,
//         v: Self::SType<'s>,
//         data: &mut O,
//         pos: usize,
//     ) -> Result<usize, SerializeError> {
//         let src: Inner::SType<'s> = self.mapper.backward(v)?.into();
//         self.inner.serialize(src, data, pos)
//     }
// }

/// Combinator that refines the result of an `inner` combinator with a predicate.
pub struct Refined<Inner, P> {
    /// The combinator whose output will be checked.
    pub inner: Inner,
    /// Predicate that must accept the parsed value.
    pub predicate: P,
}

impl<I, O, Inner, P> Combinator<I, O> for Refined<Inner, P>
where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    P: for<'s> Fn(Inner::SType<'s>) -> bool,
    for<'s> Inner::SType<'s>: FromRef<'s, Inner::Type>,
{
    type Type = Inner::Type;
    type SType<'s> = Inner::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        self.inner.length(v)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
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
    ) -> Result<usize, SerializeError> {
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

impl<I, O, Inner> Combinator<I, O> for Cond<Inner>
where
    I: VestInput,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
{
    type Type = Inner::Type;
    type SType<'s> = Inner::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        self.inner.length(v)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        if self.cond {
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
    ) -> Result<usize, SerializeError> {
        if self.cond {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::Other("condition not satisfied".into()))
        }
    }
}

/// Combinator that chains a variable-length parser with a parser for its contents.
pub struct AndThen<Prev, Next>(pub Prev, pub Next);

impl<I, O, Next> Combinator<I, O> for AndThen<Variable, Next>
where
    I: VestInput,
    O: VestOutput<I>,
    Next: Combinator<I, O>,
{
    type Type = Next::Type;
    type SType<'s> = Next::SType<'s>;

    fn length<'s>(&self, v: Self::SType<'s>) -> usize {
        self.0 .0.max(self.1.length(v))
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, chunk) = <Variable as Combinator<I, O>>::parse(&self.0, s)?;
        let (m, value) = self.1.parse(chunk)?;
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
    ) -> Result<usize, SerializeError> {
        self.1.serialize(v, data, pos)
    }
}
