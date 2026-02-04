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

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
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

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        loop {
            let (n, v) = self.inner.generate(g)?;
            if (self.predicate)(Inner::SType::ref_to_stype(&v)) {
                return Ok((n, v));
            }
        }
    }
}

/// Runtime value that can either own a value or borrow an external mutable location.
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq)]
pub enum RuntimeValue<'a, T> {
    Value(T),
    Ref(&'a mut T),
}

#[allow(missing_docs)]
impl<'a, T> RuntimeValue<'a, T> {
    pub fn from_value(v: T) -> Self {
        RuntimeValue::Value(v)
    }

    pub fn from_mut(ptr: &'a mut T) -> Self {
        RuntimeValue::Ref(ptr)
    }

    pub fn as_ref(&self) -> &T {
        match self {
            RuntimeValue::Value(v) => v,
            RuntimeValue::Ref(v) => &**v,
        }
    }

    pub fn as_mut(&mut self) -> &mut T {
        match self {
            RuntimeValue::Value(v) => v,
            RuntimeValue::Ref(v) => &mut **v,
        }
    }
}

#[allow(missing_docs)]
impl<'a> RuntimeValue<'a, u16> {
    pub fn from_u16_mut(ptr: &'a mut u16) -> Self {
        RuntimeValue::Ref(ptr)
    }
}

/// Combinator that runs its inner combinator only when `lhs` equals `rhs`.
pub struct CondEq<'a, T, Inner> {
    /// The left-hand side of the equality comparison.
    pub lhs: RuntimeValue<'a, T>,
    /// The right-hand side of the equality comparison.
    pub rhs: T,
    /// The conditional combinator.
    pub inner: Inner,
}

impl<'a, I, O, T, Inner> Combinator<I, O> for CondEq<'a, T, Inner>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    T: PartialEq + Copy,
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
        if *self.lhs.as_ref() == self.rhs {
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
        self.inner.serialize(v, data, pos)
    }

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        *self.lhs.as_mut() = self.rhs;
        self.inner.generate(g)
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

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        self.1.generate(g)
    }
}

/// Length value that may live internally or as an external mutable reference
#[derive(Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Length<'a> {
    Value(usize),
    RefU8(&'a mut u8),
    RefU16(&'a mut u16),
    RefU32(&'a mut u32),
    RefU64(&'a mut u64),
}

#[allow(missing_docs)]
impl<'a> Length<'a> {
    pub fn from_value(v: usize) -> Self {
        Length::Value(v)
    }

    pub fn from_u8_mut(ptr: &'a mut u8) -> Self {
        Length::RefU8(ptr)
    }

    pub fn from_u16_mut(ptr: &'a mut u16) -> Self {
        Length::RefU16(ptr)
    }

    pub fn from_u32_mut(ptr: &'a mut u32) -> Self {
        Length::RefU32(ptr)
    }

    pub fn from_u64_mut(ptr: &'a mut u64) -> Self {
        Length::RefU64(ptr)
    }

    pub fn get(&self) -> usize {
        match self {
            Length::Value(v) => *v,
            Length::RefU8(p) => **p as usize,
            Length::RefU16(p) => **p as usize,
            Length::RefU32(p) => **p as usize,
            Length::RefU64(p) => **p as usize,
        }
    }

    pub fn set(&mut self, v: usize) {
        match self {
            Length::Value(val) => *val = v,
            Length::RefU8(p) => **p = v as u8,
            Length::RefU16(p) => **p = v as u16,
            Length::RefU32(p) => **p = v as u32,
            Length::RefU64(p) => **p = v as u64,
        }
    }
}

/// Combinator that makes sure `Inner` parses/serializes exactly `n` bytes.
pub struct FixedLen<'a, Inner>(pub Length<'a>, pub Inner);

impl<'a, I, O, Inner> Combinator<I, O> for FixedLen<'a, Inner>
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

    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.1.length(v)
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, chunk) = <_ as Combinator<I, O>>::parse(&Variable(self.0.get()), s)?;
        let (m, value) = self.1.parse(&chunk)?;
        if m == n {
            Ok((n, value))
        } else {
            Err(ParseError::FixedLenViolation)
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

    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let (n, v) = self.1.generate(g)?;
        self.0.set(n);
        Ok((n, v))
    }
}
