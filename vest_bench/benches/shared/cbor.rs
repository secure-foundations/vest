//! Untimed, independent value and consumption checks for the CBOR workloads.

use ciborium::value::Value;
use serde::Deserialize;
use vest_lib::cbor::{CborBytes, CborFloat, CborText, CborValue};

pub fn semantic_value(value: &CborValue<'_>) -> Value {
    match value {
        CborValue::Integer(n) => Value::Integer((*n).try_into().unwrap()),
        CborValue::Bytes(bytes) => Value::Bytes(match bytes {
            CborBytes::Definite(bytes) => bytes.to_vec(),
            CborBytes::Indefinite(bytes) => bytes.clone(),
        }),
        CborValue::Text(text) => Value::Text(match text {
            CborText::Definite(text) => (*text).to_owned(),
            CborText::Indefinite(text) => text.clone(),
        }),
        CborValue::Array(values) => Value::Array(values.iter().map(semantic_value).collect()),
        CborValue::Map(values) => Value::Map(
            values
                .iter()
                .map(|(k, v)| (semantic_value(k), semantic_value(v)))
                .collect(),
        ),
        CborValue::Tag(tag, value) => Value::Tag(*tag, Box::new(semantic_value(value))),
        CborValue::Float(CborFloat::F16(bits)) => {
            let bytes = bits.to_be_bytes();
            // Let the independent decoder interpret binary16, which Rust
            // cannot convert with a standard-library floating-point type.
            ciborium::from_reader(&[0xf9, bytes[0], bytes[1]][..]).unwrap()
        }
        CborValue::Float(CborFloat::F32(bits)) => Value::Float(f32::from_bits(*bits) as f64),
        CborValue::Float(CborFloat::F64(bits)) => Value::Float(f64::from_bits(*bits)),
        CborValue::Bool(value) => Value::Bool(*value),
        CborValue::Null => Value::Null,
        CborValue::Undefined | CborValue::Simple(_) => {
            panic!("this corpus contains a value not represented by ciborium::Value")
        }
    }
}

pub fn ciborium_exact(input: &[u8]) -> Value {
    let mut remaining = input;
    let value = ciborium::from_reader(&mut remaining).unwrap();
    assert!(remaining.is_empty(), "ciborium left trailing input");
    value
}

pub fn cbor4ii_exact(input: &[u8]) -> Value {
    use cbor4ii::core::dec::{Decode, Read};
    let mut reader = cbor4ii::core::utils::SliceReader::new(input);
    let value = cbor4ii::core::Value::decode(&mut reader).unwrap();
    let remaining = reader.fill(input.len()).unwrap();
    assert!(
        remaining.as_ref().is_empty(),
        "cbor4ii left trailing input: input={input:02x?}, remaining={:02x?}",
        remaining.as_ref()
    );
    cbor4ii_semantic_value(&value)
}

/// Conversion is only used in untimed validation and serializer setup.
pub fn cbor4ii_value(value: &Value) -> cbor4ii::core::Value {
    use cbor4ii::core::Value as Native;
    match value {
        Value::Null => Native::Null,
        Value::Bool(v) => Native::Bool(*v),
        Value::Integer(v) => Native::Integer((*v).into()),
        Value::Float(v) => Native::Float(*v),
        Value::Bytes(v) => Native::Bytes(v.clone()),
        Value::Text(v) => Native::Text(v.clone()),
        Value::Array(v) => Native::Array(v.iter().map(cbor4ii_value).collect()),
        Value::Map(v) => Native::Map(
            v.iter()
                .map(|(k, v)| (cbor4ii_value(k), cbor4ii_value(v)))
                .collect(),
        ),
        Value::Tag(tag, v) => Native::Tag(*tag, Box::new(cbor4ii_value(v))),
        _ => panic!("unsupported CBOR value in corpus"),
    }
}

pub fn cbor4ii_semantic_value(value: &cbor4ii::core::Value) -> Value {
    use cbor4ii::core::Value as Native;
    match value {
        Native::Null => Value::Null,
        Native::Bool(v) => Value::Bool(*v),
        Native::Integer(v) => Value::Integer((*v).try_into().unwrap()),
        Native::Float(v) => Value::Float(*v),
        Native::Bytes(v) => Value::Bytes(v.clone()),
        Native::Text(v) => Value::Text(v.clone()),
        Native::Array(v) => Value::Array(v.iter().map(cbor4ii_semantic_value).collect()),
        Native::Map(v) => Value::Map(
            v.iter()
                .map(|(k, v)| (cbor4ii_semantic_value(k), cbor4ii_semantic_value(v)))
                .collect(),
        ),
        Native::Tag(tag, v) => Value::Tag(*tag, Box::new(cbor4ii_semantic_value(v))),
        _ => panic!("unsupported native CBOR value in corpus"),
    }
}

pub fn cbor4ii_parse(input: &[u8]) -> cbor4ii::core::Value {
    use cbor4ii::core::dec::Decode;
    cbor4ii::core::Value::decode(&mut cbor4ii::core::utils::SliceReader::new(input)).unwrap()
}

pub fn cbor4ii_encode(value: &cbor4ii::core::Value) -> Vec<u8> {
    use cbor4ii::core::enc::Encode;
    let mut writer = cbor4ii::core::utils::BufWriter::new(Vec::new());
    value.encode(&mut writer).unwrap();
    writer.into_inner()
}

pub fn minicbor_exact(input: &[u8]) -> Value {
    let mut decoder = minicbor_serde::Deserializer::new(input);
    let value = Value::deserialize(&mut decoder).unwrap();
    assert_eq!(
        decoder.decoder().position(),
        input.len(),
        "minicbor left trailing input"
    );
    value
}
