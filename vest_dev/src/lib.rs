#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(verus_only, feature(never_type))]
#![allow(unused_imports)]
#![allow(dead_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

/// An uninhabitable type used to represent impossible values (e.g., in [`combinators::Void`]).
#[cfg(verus_only)]
pub type Never = !;
/// An uninhabitable type used to represent impossible values (e.g., in [`combinators::Void`]).
#[cfg(not(verus_only))]
pub type Never = ::core::convert::Infallible;

pub use vest_lib::*;

// #[cfg(verus_only)]
pub mod spec_tests;
