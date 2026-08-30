//! Verified variable-width integer formats built from the core combinators.
//!
//! Fixed-width byte and integer formats live in [`crate::combinators`]. This
//! module contains reusable encodings whose representation depends on the
//! value, including base-128, base-256, Bitcoin VarInt, and unsigned LEB128.
/// Unsigned big-endian base-128 (VLQ) format.
pub mod base128;
/// Unsigned big-endian base-256 format.
pub mod base256;
/// Bitcoin VarInt format.
pub mod btcvarint;
/// Unsigned little-endian base-128 (ULEB128) format.
pub mod leb128;
