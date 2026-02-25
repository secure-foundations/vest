#![cfg_attr(verus_only, feature(never_type))]
#![allow(unused_imports)]
#![warn(missing_docs)]

#[cfg(verus_only)]
pub type Never = !;
#[cfg(not(verus_only))]
pub type Never = ::core::convert::Infallible;

pub mod combinators;
pub mod core;
#[cfg(test)]
pub mod tests;

// Keep v0 for backward compatibility if needed
// pub mod v0;
