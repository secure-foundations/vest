//! Native cbor4ii decoding/encoding into the borrowing-aware benchmark AST.
use super::BorrowedValue as Value;
use ::cbor4ii::core::{
    dec::{Decode, Error, Read},
    enc::{self, Encode, Write},
    error::Len,
    major, marker, types,
    utils::{BufWriter, SliceReader},
};
use std::{borrow::Cow, convert::Infallible};

pub fn parse(input: &[u8]) -> Result<Value<'_>, Error<Infallible>> {
    let mut reader = SliceReader::new(input);
    let value = Value::decode(&mut reader)?;
    if !reader.fill(1)?.as_ref().is_empty() {
        return Err(Error::Custom {
            name: &"trailing input",
            num: 0,
        });
    }
    Ok(value)
}

pub fn encode(value: &Value<'_>) -> Vec<u8> {
    let mut writer = BufWriter::new(Vec::new());
    value.encode(&mut writer).unwrap();
    writer.into_inner()
}

impl<'de> Decode<'de> for Value<'de> {
    fn decode<R: Read<'de>>(reader: &mut R) -> Result<Self, Error<R::Error>> {
        let name = &"borrowed-value";
        // Preserve cbor4ii's native reader/depth accounting, including in the
        // generic array/map decoders below.
        if !reader.step_in() {
            return Err(Error::DepthOverflow { name });
        }
        let result =
            (|| {
                let byte = reader
                    .fill(1)
                    .map_err(Error::Read)?
                    .as_ref()
                    .first()
                    .copied()
                    .ok_or(Error::Eof {
                        name,
                        expect: Len::Small(1),
                    })?;
                match ::cbor4ii::core::dec::if_major(byte) {
                    major::UNSIGNED => u64::decode(reader).map(|value| Self::Integer(value.into())),
                    major::NEGATIVE => types::Negative::<u64>::decode(reader)
                        .map(|value| Self::Integer(-1 - i128::from(value.0))),
                    major::BYTES => types::Bytes::<Cow<'de, [u8]>>::decode(reader)
                        .map(|value| Self::Bytes(value.0)),
                    major::STRING => Cow::<'de, str>::decode(reader).map(Self::Text),
                    major::ARRAY => Vec::<Self>::decode(reader).map(Self::Array),
                    major::MAP => types::Map::<Vec<(Self, Self)>>::decode(reader)
                        .map(|value| Self::Map(value.0)),
                    major::TAG => types::Tag::<Self>::decode(reader)
                        .map(|value| Self::Tag(value.0, Box::new(value.1))),
                    major::SIMPLE => match byte {
                        marker::FALSE | marker::TRUE => bool::decode(reader).map(Self::Bool),
                        marker::NULL => {
                            reader.advance(1);
                            Ok(Self::Null)
                        }
                        marker::UNDEFINED => {
                            reader.advance(1);
                            Ok(Self::Undefined)
                        }
                        marker::F16 => types::F16::decode(reader)
                            .map(|value| Self::Float(half::f16::from_bits(value.0).to_f64())),
                        marker::F32 => f32::decode(reader).map(|value| Self::Float(value.into())),
                        marker::F64 => f64::decode(reader).map(Self::Float),
                        _ => {
                            let value = types::Simple::decode(reader)?.0;
                            // RFC 8949 §3.3: the two-byte simple form requires a
                            // value of at least 32, not an alternate bool/null form.
                            if byte == 0xf8 && value < 32 {
                                return Err(Error::Unsupported { name, found: value });
                            }
                            Ok(Self::Simple(value))
                        }
                    },
                    _ => Err(Error::Unsupported { name, found: byte }),
                }
            })();
        reader.step_out();
        result
    }
}

impl Encode for Value<'_> {
    fn encode<W: Write>(&self, writer: &mut W) -> Result<(), enc::Error<W::Error>> {
        match self {
            Self::Integer(value) => value.encode(writer),
            Self::Bytes(value) => types::Bytes(value.as_ref()).encode(writer),
            Self::Text(value) => value.as_ref().encode(writer),
            Self::Array(values) => values.as_slice().encode(writer),
            Self::Map(values) => types::Map(values.as_slice()).encode(writer),
            Self::Tag(tag, value) => types::Tag(*tag, value.as_ref()).encode(writer),
            Self::Float(value) => value.encode(writer),
            Self::Bool(value) => value.encode(writer),
            Self::Null => types::Null.encode(writer),
            Self::Undefined => types::Undefined.encode(writer),
            Self::Simple(value) => types::Simple(*value).encode(writer),
        }
    }
}
