#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(verus_only, feature(never_type))]
#![allow(unused_imports)]
#![allow(dead_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub type Never = vest_lib::Never;

pub use vest_lib::*;

// #[cfg(verus_only)]
pub mod formats;
