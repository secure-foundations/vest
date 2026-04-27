//! # VEST++: The next generation VErified Serialization Toolkit
//!
//! Vest++ provides a library of formally verified (de-)serializer **combinators** built with
//! [Verus](https://github.com/verus-lang/verus), as well as a domain-specific language (DSL) for defining
//! complex binary data formats leveraging these formally verified combinators.
//!
//! ## Key Properties
//!
//! All Vest++ combinators are formally proven to satisfy **[Serialize-Parse Roundtrip](core::proof::SPRoundTrip)**:
//! for any value `v` consistent with a format, serializing `v` and then parsing the result recovers `v`.
//! Additionally, combinators that are proven to be **[Non-Malleable](core::proof::NonMalleable)** also satisfy
//! **[Parse-Serialize Roundtrip](core::proof::PSRoundTrip)**: parsing a buffer and then serializing the result
//! reproduces the consumed prefix of the original buffer.
//!
//! ## A Taste of the DSL and Combinators
//!
//! A simple TLV (tag-length-value) message can be expressed as
//!
//! ```vest
//! tlv = {
//!   @t: u8,
//!   @l: u16,
//!   v: [u8; @l] >>= choose(@t) {
//!     0x01 => Vec<msg1>,
//!     0x02 => msg2,
//!     0x03 => msg3,
//!     _ => void, // reject other tag values
//!   }
//! };
//! ```
//!
//! The same format can be expressed using combinators as
//!
//! ```text
//! let tlv =
//!     Implicit(
//!     (U8, U16Le),
//!     TLVOf(
//!       TVOr(0x01, RepeatUntilEof(Msg1),
//!       TVOr(0x02, Msg2,
//!       TVOr(0x03, Msg3,
//!       Uninhabited()))))
//! );
//! ```
//!
//! See the [`combinators`] module for the full catalog of available combinators.
// #![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(verus_only, feature(never_type))]
#![allow(unused_imports)]
#![allow(dead_code)]
// #![warn(missing_docs)]
#![allow(rustdoc::broken_intra_doc_links)]

#[cfg(feature = "alloc")]
extern crate alloc;

/// An uninhabitable type used to represent impossible values (e.g., in [`combinators::Void`]).
#[cfg(verus_only)]
pub type Never = !;
/// An uninhabitable type used to represent impossible values (e.g., in [`combinators::Void`]).
#[cfg(not(verus_only))]
pub type Never = ::core::convert::Infallible;

pub mod asn1;
pub mod combinators;
pub mod core;
