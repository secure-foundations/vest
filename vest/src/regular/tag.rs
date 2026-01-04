use alloc::vec::Vec;

use super::{bytes, leb128, leb128::UInt, uints::*};
use crate::properties::*;

/// Combinator that matches a fixed value and discards it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag<Inner, T> {
    /// Combinator that parses/serializes the tag value.
    pub inner: Inner,
    /// Value that must appear in the input.
    pub tag: T,
}

impl<Inner, T> Tag<Inner, T> {
    /// Construct a new `Tag` combinator.
    pub fn new(inner: Inner, tag: T) -> Self {
        Self { inner, tag }
    }
}

/// Generic implementation for combinators that parse/serialize owned values (e.g., integers).
impl<'x, I, O, Inner, T> Combinator<'x, I, O> for Tag<Inner, T>
where
    I: VestPublicInput,
    O: VestPublicOutput<I>,
    Inner: Combinator<'x, I, O, Type = T, SType = T>,
    T: Clone + PartialEq,
{
    type Type = ();
    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        self.inner.length(self.tag.clone())
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, value) = self.inner.parse(s)?;
        if value == self.tag {
            Ok((n, ()))
        } else {
            Err(ParseError::Other("tag mismatch".into()))
        }
    }

    fn serialize(&self, _v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        self.inner.serialize(self.tag.clone(), data, pos)
    }
}

/// Specialized implementation for fixed byte tags using `Fixed<N>`.
impl<'x, const N: usize> Combinator<'x, &'x [u8], Vec<u8>> for Tag<bytes::Fixed<N>, [u8; N]> {
    type Type = ();
    type SType = ();

    fn length(&self, _v: Self::SType) -> usize {
        N
    }

    fn parse(&self, s: &'x [u8]) -> Result<(usize, Self::Type), ParseError> {
        if s.len() < N {
            return Err(ParseError::UnexpectedEndOfInput);
        }

        let prefix = &s[..N];
        if prefix == self.tag {
            Ok((N, ()))
        } else {
            Err(ParseError::Other("tag mismatch".into()))
        }
    }

    fn serialize(&self, _v: Self::SType, data: &mut Vec<u8>, pos: usize) -> Result<usize, SerializeError> {
        if N <= data.len().saturating_sub(pos) {
            data[pos..pos + N].copy_from_slice(&self.tag);
            Ok(N)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

/// Convenience constructors for common integer tags.
/// These are helpers over `Tag::new` for built-in integer formats.
pub fn tag_u8(tag: u8) -> Tag<U8, u8> {
    Tag::new(U8, tag)
}

/// Match a little-endian `u16` tag.
pub fn tag_u16_le(tag: u16) -> Tag<U16Le, u16> {
    Tag::new(U16Le, tag)
}

/// Match a little-endian `u32` tag.
pub fn tag_u32_le(tag: u32) -> Tag<U32Le, u32> {
    Tag::new(U32Le, tag)
}

/// Match a little-endian `u64` tag.
pub fn tag_u64_le(tag: u64) -> Tag<U64Le, u64> {
    Tag::new(U64Le, tag)
}

/// Match a big-endian `u16` tag.
pub fn tag_u16_be(tag: u16) -> Tag<U16Be, u16> {
    Tag::new(U16Be, tag)
}

/// Match a big-endian `u32` tag.
pub fn tag_u32_be(tag: u32) -> Tag<U32Be, u32> {
    Tag::new(U32Be, tag)
}

/// Match a big-endian `u64` tag.
pub fn tag_u64_be(tag: u64) -> Tag<U64Be, u64> {
    Tag::new(U64Be, tag)
}

/// Match an unsigned LEB128 tag.
pub fn tag_leb128(tag: UInt) -> Tag<leb128::UnsignedLEB128, UInt> {
    Tag::new(leb128::UnsignedLEB128, tag)
}
