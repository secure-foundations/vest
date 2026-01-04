#![crate_name = "vest_lib"]
#![crate_type = "lib"]
#![warn(missing_docs)]
#![no_std]
//! Vest is a library for parsing and serializing binary data, using combinators.
//!
//! # Background
//!
//! **Parsing and serialization of binary data**
//!
//! In the context of binary formats, parsing refers to the process of interpreting raw byte
//! sequences as structured data, while serialization refers to the reverse process of encoding
//! structured data as raw byte sequences. Binary formats are essential in domains like network
//! protocols, file systems, and embedded systems, where data is often transmitted or stored in
//! a compact binary form.
//!
//! **Formally verified parsing and serialization**
//!
//! Binary formats are notoriously difficult to parse and serialize correctly, due to the
//! complexity of the formats and the potential for errors in the implementation. Vest aims to
//! address this problem by using simple, composable parser and serializer combinators with a
//! focus on straightforward, side-effect-free Rust code. The codebase has been cleaned of Verus
//! specifications and proofs so that only the executable logic remains.
//!
//! **Parser and serializer combinators**
//!
//! It's certainly possible to implement and verify parsers and serializers for single protocol
//! formats or file formats manually, but this approach is tedious, and not reusable. Binary
//! formats often share common patterns, such as fixed-size fields, variable-size fields, a
//! sequence of fields, a tagged union of fields, etc. Vest provides a set of parser and serializer
//! combinators that can be used to build complex parsers and serializers from simple ones, where
//! the properties of the combinators are verified once and for all.
//!
//! # Example: Parsing and serializing a pair of bytes
//!
//! ```rust
//! use vest::regular::bytes::Bytes;
//!
//! let pair_of_bytes = (Bytes(1), Bytes(2));
//!
//! let input = &[0x10; 10];
//! let (consumed, (a, b)) = pair_of_bytes.parse(input)?;
//!
//! let mut output = vec![0x00; 40];
//! let written = pair_of_bytes.serialize((a, b), &mut output, 0)?;
//!
//! assert_eq!(written, consumed);
//! assert_eq!(&output[..written], &input[..written]);
//! ```
//!
//! # Example: Constructing a new combinator
//!
//! ```rust
//! use vest::regular::uints::U8;
//! use vest::regular::modifier::{Refined, Pred};
//!
//! pub struct EvenU8;
//! impl Pred<u8> for EvenU8 {
//!     fn apply(&self, i: &u8) -> bool { *i % 2 == 0 }
//! }
//!
//! let even_u8 = Refined { inner: U8, predicate: EvenU8 };
//!
//! let mut output = vec![0x00; 40];
//! let ten = 10u8;
//! let written = even_u8.serialize(ten, &mut output, 0)?;
//!
//! let (consumed, parsed) = even_u8.parse(output.as_slice())?;
//!
//! assert_eq!(written, consumed);
//! assert_eq!(parsed, ten);
//! ```

// mod examples;

#[cfg(feature = "std")]
extern crate std;

extern crate alloc;

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
