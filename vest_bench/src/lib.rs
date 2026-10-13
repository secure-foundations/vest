//! Codec fixtures and corpora shared by the benchmarks and correctness tests.

pub mod harness;
pub mod micro;
pub mod real;

#[cfg(feature = "allocation-counting")]
mod allocations;
