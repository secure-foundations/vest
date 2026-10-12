//! Codec fixtures and corpora shared by the benchmarks and correctness tests.

pub mod corpora;
pub mod generated;
pub mod micro;

pub use generated::*;

use vest_lib::core::exec::serializer::{Prepare, SerializerExt};

/// Encodes one value with its generated serializer.
///
/// The Vest encoder is the ground truth for the corpus: the wire-compatibility
/// tests then check that the hand-written codec agrees with it byte for byte.
pub fn encode<F, T>(fmt: F, v: &T) -> Vec<u8>
where
    F: Prepare<T> + SerializerExt<T> + vest_lib::core::exec::serializer::Serializer<Vec<u8>, T>,
    T: vstd::prelude::DeepView + ?Sized,
{
    let mut out = Vec::new();
    fmt.serialize_with_vec(v, &mut out);
    out
}
