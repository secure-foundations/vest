//! Generic CBOR values and their specification views.
use alloc::{boxed::Box, string::String, vec::Vec};
use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

/// A CBOR floating-point payload.
///
/// Width and raw IEEE 754 bits are retained.
/// A future deterministic floating-point layer can define and verify
/// shortest-width equivalence without changing the wire-facing value type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum CborFloat {
    F16(u16),
    F32(u32),
    F64(u64),
}

impl DeepView for CborFloat {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/// Runtime representation of a CBOR byte string.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CborBytes<'i> {
    /// A definite-length string borrowed directly from the input.
    Definite(&'i [u8]),
    /// Flattened contents of an indefinite-length, fragmented string.
    Indefinite(Vec<u8>),
}

impl<'i> DeepView for CborBytes<'i> {
    type V = Seq<u8>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Definite(bytes) => bytes.deep_view(),
            Self::Indefinite(bytes) => bytes.deep_view(),
        }
    }
}

/// Runtime representation of a CBOR text string.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CborText<'i> {
    /// A definite-length UTF-8 string borrowed directly from the input.
    Definite(&'i str),
    /// Flattened contents of an indefinite-length, fragmented string.
    Indefinite(String),
}

impl<'i> DeepView for CborText<'i> {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Definite(text) => text.deep_view(),
            Self::Indefinite(text) => text.deep_view(),
        }
    }
}

/// Runtime representation of a CBOR array.
pub type CborArray<'i> = Vec<CborValue<'i>>;

/// Runtime representation of a CBOR map.
///
/// Entries retain wire order and duplicate entries are preserved. This codec
/// recognizes well-formed CBOR; applications that require RFC 8949 basic
/// validity must additionally reject duplicate keys (section 5.3.1).
pub type CborMap<'i> = Vec<(CborValue<'i>, CborValue<'i>)>;

/// Generic CBOR value.
#[derive(Debug, PartialEq, Eq)]
pub enum CborValue<'i> {
    /// An integer in the RFC 8949 range `-2^64 ..= 2^64 - 1`.
    Integer(i128),
    Bytes(CborBytes<'i>),
    Text(CborText<'i>),
    Array(CborArray<'i>),
    Map(CborMap<'i>),
    Tag(u64, Box<CborValue<'i>>),
    Float(CborFloat),
    Bool(bool),
    Null,
    Undefined,
    /// An unassigned/registered simple value other than 20 through 23.
    Simple(u8),
}

/// Logical value used by CBOR specifications.
///
/// Definite/indefinite framing is erased, matching the RFC generic data model.
/// Floating-point width is retained.
pub enum CborValueSpec {
    Integer(i128),
    Bytes(Seq<u8>),
    Text(Seq<char>),
    Array(Seq<CborValueSpec>),
    Map(Seq<(CborValueSpec, CborValueSpec)>),
    Tag(u64, Box<CborValueSpec>),
    Float(CborFloat),
    Bool(bool),
    Null,
    Undefined,
    Simple(u8),
}

pub open spec fn cbor_value_view(value: &CborValue) -> CborValueSpec
    decreases *value,
{
    match value {
        CborValue::Integer(value) => CborValueSpec::Integer(*value),
        CborValue::Bytes(value) => CborValueSpec::Bytes(value.deep_view()),
        CborValue::Text(value) => CborValueSpec::Text(value.deep_view()),
        CborValue::Array(values) => {
            let seq = values@;
            CborValueSpec::Array(
                Seq::new(
                    seq.len(),
                    |i: int|
                        {
                            if 0 <= i < seq.len() {
                                cbor_value_view(&seq[i])
                            } else {
                                arbitrary()
                            }
                        },
                ),
            )
        },
        CborValue::Map(values) => {
            let seq = values@;
            CborValueSpec::Map(
                Seq::new(
                    seq.len(),
                    |i: int|
                        {
                            if 0 <= i < seq.len() {
                                (cbor_value_view(&seq[i].0), cbor_value_view(&seq[i].1))
                            } else {
                                arbitrary()
                            }
                        },
                ),
            )
        },
        CborValue::Tag(tag, value) => {
            CborValueSpec::Tag(*tag, Box::new(cbor_value_view(&**value)))
        },
        CborValue::Float(value) => CborValueSpec::Float(*value),
        CborValue::Bool(value) => CborValueSpec::Bool(*value),
        CborValue::Null => CborValueSpec::Null,
        CborValue::Undefined => CborValueSpec::Undefined,
        CborValue::Simple(value) => CborValueSpec::Simple(*value),
    }
}

impl<'i> DeepView for CborValue<'i> {
    type V = CborValueSpec;

    open spec fn deep_view(&self) -> Self::V {
        cbor_value_view(self)
    }
}

/// Connects the explicit structurally-recursive collection view above to the
/// standard `Vec<T>::deep_view` used by executable repeat combinators.
pub proof fn lemma_collection_value_view(value: &CborValue)
    ensures
        match value {
            CborValue::Array(values) => {
                cbor_value_view(value) == CborValueSpec::Array(values.deep_view())
            },
            CborValue::Map(entries) => {
                cbor_value_view(value) == CborValueSpec::Map(entries.deep_view())
            },
            _ => true,
        },
    decreases *value,
{
    match value {
        CborValue::Array(values) => {
            let viewed = cbor_value_view(value);
            let actual = match viewed {
                CborValueSpec::Array(s) => s,
                _ => arbitrary(),
            };
            assert_seqs_equal!(actual, values.deep_view(), i => {});
            assert(viewed == CborValueSpec::Array(actual));
        },
        CborValue::Map(entries) => {
            let viewed = cbor_value_view(value);
            let actual = match viewed {
                CborValueSpec::Map(s) => s,
                _ => arbitrary(),
            };
            assert_seqs_equal!(actual, entries.deep_view(), i => {});
            assert(viewed == CborValueSpec::Map(actual));
        },
        _ => {},
    }
}

} // verus!
