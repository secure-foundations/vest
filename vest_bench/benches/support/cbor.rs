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
    use cbor4ii::core::dec::Read;
    let reader = cbor4ii::core::utils::SliceReader::new(input);
    let mut decoder = cbor4ii::serde::Deserializer::new(reader);
    let value = Value::deserialize(&mut decoder).unwrap();
    let mut reader = decoder.into_inner();
    let remaining = reader.fill(input.len()).unwrap();
    assert!(
        remaining.as_ref().is_empty(),
        "cbor4ii left trailing input: input={input:02x?}, remaining={:02x?}",
        remaining.as_ref()
    );
    value
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
