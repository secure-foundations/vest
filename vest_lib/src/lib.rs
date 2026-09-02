//! # `vest_lib`
//!
//! `vest_lib` is Vest's format combinator
//! library verified in [Verus](https://github.com/verus-lang/verus).
//! A format in Vest is organized in three layers:
//!
//! - pure parsing, serialization, byte-length, and consistency specifications
//!   in [`core::spec`];
//! - executable parsing and serialization APIs in [`core::exec`]; and
//! - correctness and security theorems in [`core::proof`].
//!
//! ## Where to start
//!
//! - [`core`] includes Vest's core specs as well as the runtime API and buffer abstractions.
//! - [`combinators`] documents all the primitive and higher-order formats.
//! - [`asn1`] contains modular DER and BER formats.
//! - [`cbor`] provides generic CBOR formats for both general and deterministic profiles.
//! - [`primitives`] contains reusable variable-width integer formats.
//!
//! See the [Vest guide](https://secure-foundations.github.io/vest/guide/) for more background and
//! gentle introductions.
//!
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(verus_only, feature(never_type))]
#![allow(unused_imports)]
#![allow(dead_code)]
// Enable once proof-internal helper items are hidden from the public rustdoc surface.
// #![warn(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Unit tests run on a host with `std` even when checking the library's core-only feature set.
// Import its macros so allocation-free APIs can still be exercised by ordinary test fixtures.
#[cfg(all(test, not(feature = "std")))]
#[macro_use]
extern crate std;

/// An uninhabitable type used to represent impossible values (e.g., in [`combinators::Void`]).
pub type Never = combinators::marker::exec::ExecNever;

pub mod asn1;
#[cfg(feature = "alloc")]
pub mod cbor;
pub mod combinators;
pub mod core;
pub mod macros;
pub mod primitives;
