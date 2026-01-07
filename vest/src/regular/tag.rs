use crate::{
    buf_traits::{VestInput, VestOutput},
    errors::{GenerateError, ParseError, SerializeError},
    properties::{Combinator, GResult, GenSt},
    regular::sequence::{FromRef, UnitCombinator},
};

/// Tag combinator that associates a tag value with an inner combinator.
pub struct Tag<Inner, T> {
    /// The inner combinator.
    pub inner: Inner,
    /// The tag value.
    pub tag: T,
}

impl<Inner, T> Tag<Inner, T> {
    /// Create a new `Tag` combinator.
    pub fn new(inner: Inner, tag: T) -> Self {
        Self { inner, tag }
    }
}

/// Comparison trait used by `Tag`.
pub trait Compare<T> {
    /// Compare self with another value of type T.
    fn compare(&self, other: &T) -> bool;
}

impl<T: Copy + PartialEq> Compare<T> for T {
    fn compare(&self, other: &T) -> bool {
        *self == *other
    }
}

impl<'i, const N: usize> Compare<&'i [u8]> for [u8; N] {
    fn compare(&self, other: &&'i [u8]) -> bool {
        if other.len() != N {
            return false;
        }
        for i in 0..N {
            if self[i] != other[i] {
                return false;
            }
        }
        true
    }
}

impl<I, O, Inner, T> Combinator<I, O> for Tag<Inner, T>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    T: for<'s> Compare<Inner::SType<'s>> + Copy,
    for<'p, 's> Inner::SType<'s>:
        FromRef<'s, Inner::Type<'p>> + FromRef<'s, Inner::GType> + From<T>,
{
    type Type<'p>
        = ()
    where
        I: 'p;
    type SType<'s>
        = ()
    where
        I: 's;
    type GType = ();

    fn length<'s>(&self, _: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        self.inner.length(self.tag.into())
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        let (n, v) = self.inner.parse(s)?;
        if self.tag.compare(&Inner::SType::ref_to_stype(&v)) {
            Ok((n, ()))
        } else {
            Err(ParseError::TagMismatch)
        }
    }

    fn serialize<'s>(
        &self,
        _: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        self.inner.serialize(self.tag.into(), data, pos)
    }

    fn generate(&self, _g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        let n = self.length(());
        Ok((n, ()))
    }
}

impl<I, O, Inner, T> UnitCombinator<I, O> for Tag<Inner, T>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Inner: Combinator<I, O>,
    T: for<'s> Compare<Inner::SType<'s>> + Copy,
    for<'p, 's> Inner::SType<'s>:
        FromRef<'s, Inner::Type<'p>> + FromRef<'s, Inner::GType> + From<T>,
{
    fn parse_unit<'p>(&self, s: &'p I) -> Result<usize, ParseError>
    where
        I: 'p,
    {
        let (n, _) = self.parse(s)?;
        Ok(n)
    }

    fn serialize_unit<'s>(&self, data: &mut O, pos: usize) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        self.serialize((), data, pos)
    }

    fn length_unit(&self) -> usize {
        self.inner.length(self.tag.into())
    }
}
