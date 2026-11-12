//! Shared benchmark AST: borrow definite strings, flatten fragmented strings.
//!
//! Maps preserve entry order and duplicates. Like the former native baseline
//! values, floating-point numbers are represented numerically as `f64`.
use std::borrow::Cow;

#[derive(Clone, Debug, PartialEq)]
pub enum Value<'i> {
    Integer(i128),
    Bytes(Cow<'i, [u8]>),
    Text(Cow<'i, str>),
    Array(Vec<Self>),
    Map(Vec<(Self, Self)>),
    Tag(u64, Box<Self>),
    Float(f64),
    Bool(bool),
    Null,
    Undefined,
    Simple(u8),
}

impl Value<'_> {
    /// An owned reference value, only constructed in untimed correctness checks.
    pub fn semantic_value(&self) -> ciborium::Value {
        use ciborium::Value as Reference;
        match self {
            Self::Integer(value) => Reference::Integer((*value).try_into().unwrap()),
            Self::Bytes(bytes) => Reference::Bytes(bytes.to_vec()),
            Self::Text(text) => Reference::Text(text.to_string()),
            Self::Array(values) => {
                Reference::Array(values.iter().map(Self::semantic_value).collect())
            }
            Self::Map(values) => Reference::Map(
                values
                    .iter()
                    .map(|(key, value)| (key.semantic_value(), value.semantic_value()))
                    .collect(),
            ),
            Self::Tag(tag, value) => Reference::Tag(*tag, Box::new(value.semantic_value())),
            Self::Float(value) => Reference::Float(*value),
            Self::Bool(value) => Reference::Bool(*value),
            Self::Null => Reference::Null,
            Self::Undefined | Self::Simple(_) => {
                panic!("this corpus contains a value not represented by ciborium::Value")
            }
        }
    }
}
