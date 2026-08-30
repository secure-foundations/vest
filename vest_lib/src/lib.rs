//! # `vest_lib`
//!
//! `vest_lib` is Vest's formally verified parser and serializer combinator
//! library for [Verus](https://github.com/verus-lang/verus). A format can
//! provide three related layers:
//!
//! - pure parsing, serialization, byte-length, and consistency specifications
//!   in [`core::spec`];
//! - executable parsing, preparation, and destination-passing serialization in
//!   [`core::exec`]; and
//! - compositional correctness and security theorems in [`core::proof`].
//!
//! The executable serializer is intentionally infallible. Call
//! [`Prepare::prepare`](core::exec::Prepare::prepare) first to validate the
//! value and obtain its exact byte length, then use
//! [`SerializerExt::serialize`](core::exec::SerializerExt::serialize) with an
//! exactly sized caller-provided slice. Parsing returns both the consumed
//! length and a value, allowing formats that intentionally leave trailing
//! input.
//!
//! ## Where to start
//!
//! - [`combinators`] catalogs the primitive and higher-order formats.
//! - [`core::exec`] documents the runtime API and buffer abstractions.
//! - [`core::proof`] gives the exact round-trip and security properties.
//! - [`asn1`] contains modular DER and BER formats.
//! - [`cbor`] provides generic general and deterministic CBOR when `alloc` is
//!   enabled.
//! - [`primitives`] contains reusable variable-width integer formats.
//!
//! The [Vest guide](https://secure-foundations.github.io/vest/guide/) contains
//! tutorials, a plain-language account of the guarantees, and guidance for the
//! DSL, ASN.1 frontend, and CBOR codec. Most application schemas should use the
//! DSL or ASN.1 frontend instead of spelling large combinator types manually.
//!
//! ## Features
//!
//! The default `std` feature includes allocation-backed formats and detailed
//! error traces. `alloc` supports owned and recursive values without `std`.
//! With default features disabled, the remaining library is `core`-only and
//! still supports caller-provided input and output slices.
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
