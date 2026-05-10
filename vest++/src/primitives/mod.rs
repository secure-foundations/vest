//! Primitive formats built from the core Vest++ combinators.
/// Unsigned big-endian base-128 (VLQ) format.
pub mod base128;
/// Unsigned big-endian base-256 format.
pub mod base256;
/// Bitcoin VarInt format.
pub mod btcvarint;
/// Unsigned little-endian base-128 (ULEB128) format.
pub mod leb128;
