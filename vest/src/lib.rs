#![crate_name = "vest_lib"]
#![crate_type = "lib"]
#![warn(missing_docs)]
#![no_std]
#![doc = include_str!("lib.md")]

// mod examples;

#[cfg(feature = "std")]
extern crate std;

extern crate alloc;

/// Combinators for Bitcoin formats.
pub mod bitcoin;
/// Definitions for buffer traits that can be used as input and output for parsers and serializers,
/// along with some implementations for commonly used buffers.
pub mod buf_traits;
/// Definitions for parser and serializer combinators and their properties.
pub mod properties;
/// Regular parser and serializer combinators.
pub mod regular;
/// Utility functions and types.
pub mod utils;
//// Constant-time parser and serializer combinators.
// mod secret;
/// Error types
#[allow(missing_docs)]
pub mod errors;
