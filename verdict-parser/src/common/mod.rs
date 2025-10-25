#![allow(unused_imports)]

pub(crate) use verdict_macros::PolyfillClone;
pub(crate) use verdict_macros::View;
/// Common operators, some from Vest
pub(crate) use verdict_polyfill::*;

mod base64;
mod cached;
mod clone;
mod default;
mod depend;
mod end;
mod eq;
mod mapper;
mod option_deep;
mod optional;
mod pair;  // Keep for PairValue type definition
// mod repeat;  // Use vest's Repeat instead
mod unreachable;
mod vec_deep;
mod vest;
mod wrapped;

pub use base64::*;
pub use cached::*;
pub use clone::*;
pub use default::*;
pub use depend::*;
pub use end::*;
pub use eq::*;
pub use mapper::*;
pub use option_deep::*;
pub use optional::*;
pub use pair::PairValue;  // Only export PairValue, not Pair (use vest's Pair)
// pub use repeat::*;  // Use vest's Repeat instead
pub use unreachable::*;
pub use vec_deep::*;
pub use vest::*;  // This already exports Pair and Repeat from vest
pub use wrapped::*;

