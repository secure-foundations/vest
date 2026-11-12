//! Native minicbor decoding/encoding into the borrowing-aware benchmark AST.
use super::BorrowedValue as Value;
use ::minicbor::{
    data::{Int, Tag, Type},
    decode::{self, Decoder},
    encode::{self, Encoder, Write},
    Decode, Encode,
};
use std::borrow::Cow;

// Bound recursive AST construction, including malformed inputs. Tokenization
// and skip() do not construct/check the same tree and are not used here.
const MAX_DEPTH: usize = 256;

pub fn parse(input: &[u8]) -> Result<Value<'_>, decode::Error> {
    let mut decoder = Decoder::new(input);
    let mut remaining = MAX_DEPTH;
    let value = decoder.decode_with(&mut remaining)?;
    if decoder.position() != input.len() {
        return Err(decode::Error::message("trailing input"));
    }
    Ok(value)
}

pub fn encode(value: &Value<'_>) -> Vec<u8> {
    ::minicbor::to_vec(value).unwrap()
}

impl<'de> Decode<'de, usize> for Value<'de> {
    fn decode(decoder: &mut Decoder<'de>, remaining: &mut usize) -> Result<Self, decode::Error> {
        if *remaining == 0 {
            return Err(decode::Error::message("depth limit exceeded"));
        }
        *remaining -= 1;
        let result = (|| match decoder.datatype()? {
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::Int => decoder.int().map(|value| Self::Integer(value.into())),
            Type::Bytes => decoder
                .bytes()
                .map(|value| Self::Bytes(Cow::Borrowed(value))),
            Type::String => decoder.str().map(|value| Self::Text(Cow::Borrowed(value))),
            Type::BytesIndef => {
                let mut bytes = Vec::new();
                for part in decoder.bytes_iter()? {
                    bytes.extend_from_slice(part?);
                }
                Ok(Self::Bytes(Cow::Owned(bytes)))
            }
            Type::StringIndef => {
                let mut text = String::new();
                for part in decoder.str_iter()? {
                    text.push_str(part?);
                }
                Ok(Self::Text(Cow::Owned(text)))
            }
            Type::Array | Type::ArrayIndef => decoder
                .array_iter_with(remaining)?
                .collect::<Result<Vec<Self>, _>>()
                .map(Self::Array),
            Type::Map | Type::MapIndef => decoder
                .map_iter_with(remaining)?
                .collect::<Result<Vec<(Self, Self)>, _>>()
                .map(Self::Map),
            Type::Tag => {
                let tag = decoder.tag()?.as_u64();
                let value = decoder.decode_with(remaining)?;
                Ok(Self::Tag(tag, Box::new(value)))
            }
            Type::Bool => decoder.bool().map(Self::Bool),
            Type::Null => decoder.null().map(|_| Self::Null),
            Type::Undefined => decoder.undefined().map(|_| Self::Undefined),
            Type::Simple => {
                let start = decoder.position();
                let value = decoder.simple()?;
                if decoder.position() - start == 2 && value < 32 {
                    return Err(decode::Error::message("invalid two-byte simple value"));
                }
                Ok(Self::Simple(value))
            }
            Type::F16 | Type::F32 | Type::F64 => decoder.f64().map(Self::Float),
            _ => Err(decode::Error::message("unexpected CBOR item")),
        })();
        *remaining += 1;
        result
    }
}

impl<C> Encode<C> for Value<'_> {
    fn encode<W: Write>(
        &self,
        encoder: &mut Encoder<W>,
        context: &mut C,
    ) -> Result<(), encode::Error<W::Error>> {
        match self {
            Self::Integer(value) => {
                let value = Int::try_from(*value)
                    .map_err(|_| encode::Error::message("integer outside CBOR range"))?;
                encoder.int(value)?;
            }
            Self::Bytes(value) => {
                encoder.bytes(value)?;
            }
            Self::Text(value) => {
                encoder.str(value)?;
            }
            Self::Array(values) => {
                encoder.array(values.len() as u64)?;
                for value in values {
                    encoder.encode_with(value, context)?;
                }
            }
            Self::Map(values) => {
                encoder.map(values.len() as u64)?;
                for (key, value) in values {
                    encoder.encode_with(key, context)?;
                    encoder.encode_with(value, context)?;
                }
            }
            Self::Tag(tag, value) => {
                encoder.tag(Tag::new(*tag))?;
                encoder.encode_with(value.as_ref(), context)?;
            }
            Self::Float(value) => {
                encoder.f64(*value)?;
            }
            Self::Bool(value) => {
                encoder.bool(*value)?;
            }
            Self::Null => {
                encoder.null()?;
            }
            Self::Undefined => {
                encoder.undefined()?;
            }
            Self::Simple(value) => {
                encoder.simple(*value)?;
            }
        }
        Ok(())
    }
}
