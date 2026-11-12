//! CBOR corpora, borrowing-aware native baseline adapters, and wire checks.

use ciborium::value::Value;
use std::fs;
use vest_lib::cbor::CborFmt;
use vest_lib::cbor::{CborBytes, CborFloat, CborText, CborValue};
use vest_lib::core::exec::{Prepare, SerializerExt};

pub mod cbor4ii;
pub mod minicbor;
mod value;

pub use value::Value as BorrowedValue;

fn nested(depth: usize, seed: i64) -> Value {
    if depth == 0 {
        Value::Integer(seed.into())
    } else {
        Value::Map(vec![
            (
                Value::Text("depth".into()),
                Value::Integer((depth as i64).into()),
            ),
            (Value::Text("payload".into()), nested(depth - 1, seed)),
            (Value::Text("ok".into()), Value::Bool(depth % 2 == 0)),
        ])
    }
}

pub fn synthetic_values() -> Vec<Value> {
    let mut values = Vec::new();
    for seed in 0..256i64 {
        values.push(Value::Integer(seed.into()));
        values.push(Value::Integer((-seed - 1).into()));
        values.push(Value::Bytes(
            (0..seed as usize % 128)
                .map(|i| (i ^ seed as usize) as u8)
                .collect(),
        ));
        values.push(Value::Text(format!(
            "Vest-CBOR-{seed:04}-{}",
            "x".repeat(seed as usize % 96)
        )));
        values.push(Value::Array(
            (0..seed as usize % 24)
                .map(|i| Value::Integer(((seed as usize * 31 + i) as i64).into()))
                .collect(),
        ));
        values.push(nested(4, seed));
    }
    values
}

fn canonical(value: &Value) -> Vec<u8> {
    let mut bytes = Vec::new();
    ciborium::into_writer(value, &mut bytes).unwrap();
    bytes
}

fn cbor_head(major: u8, argument: usize) -> Vec<u8> {
    let mut out = vec![(major << 5) | 27];
    out.extend_from_slice(&(argument as u64).to_be_bytes());
    out
}

fn fragmented(major: u8, bytes: &[u8]) -> Vec<u8> {
    let first = bytes.len() / 3;
    let second = bytes.len() * 2 / 3;
    let mut out = vec![(major << 5) | 31];
    for chunk in [&bytes[..first], &bytes[first..second], &bytes[second..]] {
        out.extend_from_slice(&cbor_head(major, chunk.len()));
        out.extend_from_slice(chunk);
    }
    out.push(0xff);
    out
}

pub fn malleable(value: &Value) -> Vec<u8> {
    match value {
        Value::Integer(_) => {
            let bytes = canonical(value);
            let major = bytes[0] >> 5;
            let additional = bytes[0] & 31;
            let argument = match additional {
                0..=23 => additional as u64,
                24 => bytes[1] as u64,
                25 => u16::from_be_bytes(bytes[1..3].try_into().unwrap()) as u64,
                26 => u32::from_be_bytes(bytes[1..5].try_into().unwrap()) as u64,
                27 => u64::from_be_bytes(bytes[1..9].try_into().unwrap()),
                _ => unreachable!(),
            };
            let mut out = vec![(major << 5) | 27];
            out.extend_from_slice(&argument.to_be_bytes());
            out
        }
        Value::Bytes(bytes) => fragmented(2, bytes),
        Value::Text(text) => fragmented(3, text.as_bytes()),
        Value::Array(items) => {
            let mut out = vec![0x9f];
            for item in items {
                out.extend(malleable(item));
            }
            out.push(0xff);
            out
        }
        Value::Map(entries) => {
            let mut out = vec![0xbf];
            for (key, value) in entries {
                out.extend(canonical(key));
                out.extend(malleable(value));
            }
            out.push(0xff);
            out
        }
        _ => canonical(value),
    }
}

fn decode_hex(text: &str) -> Vec<u8> {
    let compact: Vec<_> = text
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect();
    assert_eq!(compact.len() % 2, 0, "odd-length hex input");
    compact
        .chunks_exact(2)
        .map(|pair| {
            let digit = |byte: u8| match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => panic!("invalid hex digit"),
            };
            digit(pair[0]) << 4 | digit(pair[1])
        })
        .collect()
}

pub fn cose_inputs() -> Vec<Vec<u8>> {
    let mut paths = super::files(&super::corpora_dir().join("cbor/cose-wg"), "json");
    paths.sort();
    paths
        .into_iter()
        .filter_map(|path| {
            let document: serde_json::Value =
                serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
            document
                .pointer("/output/cbor")
                .and_then(|value| value.as_str())
                .map(decode_hex)
        })
        .collect()
}

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

pub struct Values<'i> {
    pub vest: Vec<CborValue<'i>>,
    pub cbor4ii: Vec<BorrowedValue<'i>>,
    pub minicbor: Vec<BorrowedValue<'i>>,
}

/// Validate parsing and equal serialized output while constructing values once.
pub fn validated_values<'i>(values: &[Value], inputs: &'i [Vec<u8>]) -> Values<'i> {
    assert!(!inputs.is_empty());
    assert_eq!(values.len(), inputs.len());
    let format = CborFmt::<false>;
    let mut result = Values {
        vest: Vec::new(),
        cbor4ii: Vec::new(),
        minicbor: Vec::new(),
    };
    for (expected, input) in values.iter().zip(inputs) {
        assert_eq!(&ciborium_exact(input), expected);
        let minicbor = minicbor::parse(input).unwrap();
        assert_eq!(&minicbor.semantic_value(), expected);
        let cbor4ii = cbor4ii::parse(input).unwrap();
        assert_eq!(&cbor4ii.semantic_value(), expected);
        let value = crate::harness::parse_complete(&format, input).unwrap();
        assert_eq!(&semantic_value(&value), expected);
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, &mut output);
        assert_eq!(&ciborium_exact(&output), expected);
        assert_eq!(output, canonical(expected));
        assert_eq!(output, cbor4ii::encode(&cbor4ii));
        assert_eq!(output, minicbor::encode(&minicbor));
        result.vest.push(value);
        result.cbor4ii.push(cbor4ii);
        result.minicbor.push(minicbor);
    }
    result
}
