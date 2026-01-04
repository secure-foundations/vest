use crate::properties::*;

/// Result of UnsignedLEB128
pub type UInt = u64;

/// Unsigned LEB128 combinator.
pub struct UnsignedLEB128;

const MAX_BYTES: usize = 10;

fn has_space(buf_len: usize, pos: usize, need: usize) -> bool {
    pos.checked_add(need).map(|end| end <= buf_len).unwrap_or(false)
}

fn encoded_len(mut v: UInt) -> usize {
    let mut len = 1;
    while v >= 0x80 {
        v >>= 7;
        len += 1;
    }
    len
}

impl<'x, I, O> Combinator<'x, I, O> for UnsignedLEB128
where
    I: VestPublicInput,
    O: VestPublicOutput<I>,
{
    type Type = UInt;
    type SType = UInt;

    fn length(&self, v: Self::SType) -> usize {
        encoded_len(v)
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let bytes = s.as_byte_slice();
        let mut value: u64 = 0;
        let mut shift: u32 = 0;
        let mut consumed = 0usize;

        for &b in bytes {
            let payload = (b & 0x7f) as u64;
            if shift >= 64 || (shift == 63 && payload > 1) {
                return Err(ParseError::Other("LEB128 overflow".into()));
            }

            value |= payload << shift;
            consumed += 1;

            if b & 0x80 == 0 {
                if consumed != encoded_len(value) {
                    return Err(ParseError::Other("non-canonical LEB128".into()));
                }
                return Ok((consumed, value));
            }

            shift = shift.saturating_add(7);
            if consumed >= MAX_BYTES {
                return Err(ParseError::Other("LEB128 overflow".into()));
            }
        }

        Err(ParseError::UnexpectedEndOfInput)
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        let needed = encoded_len(v);
        if !has_space(data.len(), pos, needed) {
            return Err(SerializeError::InsufficientBuffer);
        }

        let mut remaining = v;
        for i in 0..needed {
            let byte = (remaining & 0x7f) as u8;
            remaining >>= 7;
            let out = if i + 1 < needed { byte | 0x80 } else { byte };
            data.set_byte(pos + i, out);
        }

        Ok(needed)
    }
}
