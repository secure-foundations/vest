use crate::properties::*;
use core::mem::size_of;

fn has_space(buf_len: usize, pos: usize, need: usize) -> bool {
    pos.checked_add(need)
        .map(|end| end <= buf_len)
        .unwrap_or(false)
}

/// Parse/serialize an unsigned 8-bit integer.
#[derive(Copy, Debug, Default, PartialEq, Eq)]
pub struct U8;

/// Parse/serialize an unsigned 16-bit integer (little endian).
#[derive(Copy, Debug, Default, PartialEq, Eq)]
pub struct U16Le;

/// Parse/serialize an unsigned 32-bit integer (little endian).
#[derive(Copy, Debug, Default, PartialEq, Eq)]
pub struct U32Le;

/// Parse/serialize an unsigned 64-bit integer (little endian).
#[derive(Copy, Debug, Default, PartialEq, Eq)]
pub struct U64Le;

/// Parse/serialize an unsigned 16-bit integer (big endian).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct U16Be;

/// Parse/serialize an unsigned 32-bit integer (big endian).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct U32Be;

/// Parse/serialize an unsigned 64-bit integer (big endian).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct U64Be;

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
/// Three-byte unsigned integer wrapper.
pub struct u24(pub [u8; 3]);

impl u24 {
    /// Interpret the stored bytes as a big-endian `u32`.
    pub fn as_u32(&self) -> u32 {
        ((self.0[0] as u32) << 16) | ((self.0[1] as u32) << 8) | self.0[2] as u32
    }

    /// Return bytes in big-endian order.
    pub fn to_be_bytes(self) -> [u8; 3] {
        self.0
    }

    /// Return bytes in little-endian order.
    pub fn to_le_bytes(self) -> [u8; 3] {
        [self.0[2], self.0[1], self.0[0]]
    }

    /// Construct from big-endian bytes.
    pub fn from_be_bytes(bytes: [u8; 3]) -> Self {
        u24(bytes)
    }

    /// Construct from little-endian bytes.
    pub fn from_le_bytes(bytes: [u8; 3]) -> Self {
        u24([bytes[2], bytes[1], bytes[0]])
    }
}

/// Parse/serialize a little-endian 24-bit integer.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct U24Le;

/// Parse/serialize a big-endian 24-bit integer.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct U24Be;

fn parse_int<const N: usize, T, I>(
    s: &I,
    f: impl Fn([u8; N]) -> T,
) -> Result<(usize, T), ParseError>
where
    I: VestPublicInput + ?Sized,
{
    if s.len() < N {
        return Err(ParseError::UnexpectedEndOfInput);
    }
    let mut bytes = [0u8; N];
    bytes.copy_from_slice(&s.as_byte_slice()[..N]);
    Ok((N, f(bytes)))
}

fn serialize_int<const N: usize, I, O>(
    bytes: [u8; N],
    data: &mut O,
    pos: usize,
) -> Result<usize, SerializeError>
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    if has_space(data.len(), pos, N) {
        data.set_byte_range(pos, &bytes);
        Ok(N)
    } else {
        Err(SerializeError::InsufficientBuffer)
    }
}

impl<I, O> Combinator<I, O> for U8
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u8
    where
        I: 'p;
    type SType<'s>
        = u8
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        1
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<1, _, _>(s, |b| b[0])
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
        serialize_int::<1, I, O>([v], data, pos)
    }
}

impl<I, O> Combinator<I, O> for U16Le
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u16
    where
        I: 'p;
    type SType<'s>
        = u16
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        size_of::<u16>()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<2, _, _>(s, |b| u16::from_le_bytes(b))
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
        serialize_int::<2, I, O>(v.to_le_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U32Le
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u32
    where
        I: 'p;
    type SType<'s>
        = u32
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        size_of::<u32>()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<4, _, _>(s, |b| u32::from_le_bytes(b))
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
        serialize_int::<4, I, O>(v.to_le_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U64Le
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u64
    where
        I: 'p;
    type SType<'s>
        = u64
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        size_of::<u64>()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<8, _, _>(s, |b| u64::from_le_bytes(b))
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
        serialize_int::<8, I, O>(v.to_le_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U16Be
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u16
    where
        I: 'p;
    type SType<'s>
        = u16
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        size_of::<u16>()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<2, _, _>(s, |b| u16::from_be_bytes(b))
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
        serialize_int::<2, I, O>(v.to_be_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U32Be
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u32
    where
        I: 'p;
    type SType<'s>
        = u32
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        size_of::<u32>()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<4, _, _>(s, |b| u32::from_be_bytes(b))
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
        serialize_int::<4, I, O>(v.to_be_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U64Be
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u64
    where
        I: 'p;
    type SType<'s>
        = u64
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        size_of::<u64>()
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<8, _, _>(s, |b| u64::from_be_bytes(b))
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
        serialize_int::<8, I, O>(v.to_be_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U24Le
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u24
    where
        I: 'p;
    type SType<'s>
        = u24
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        3
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<3, _, _>(s, |b| u24::from_le_bytes(b))
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
        serialize_int::<3, I, O>(v.to_le_bytes(), data, pos)
    }
}

impl<I, O> Combinator<I, O> for U24Be
where
    I: VestPublicInput + ?Sized,
    O: VestPublicOutput<I>,
{
    type Type<'p>
        = u24
    where
        I: 'p;
    type SType<'s>
        = u24
    where
        I: 's;

    fn length<'s>(&self, _v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        3
    }

    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        parse_int::<3, _, _>(s, |b| u24::from_be_bytes(b))
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
        serialize_int::<3, I, O>(v.to_le_bytes(), data, pos)
    }
}
