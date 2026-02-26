//! Core specifications and correctness/security theorems for Vest++ combinators.
//!
//! This module forms the foundation of the Vest++ combinator framework. It defines:
//!
//! ## [`spec`] — Specification Family of Traits
//!
//! - [`spec::SpecParser`] — parser specification
//! - [`spec::SpecSerializer`] — serializer specification
//! - [`spec::SpecSerializerDps`] — destination-passing style serializer specification
//! - [`spec::SpecByteLen`] — byte length of serialized values
//! - [`spec::Consistency`] — value well-formedness against the format specification
//! - [`spec::Unambiguity`] — conditions for unambiguous format composition
//!
//! These traits are designed to be as independent as possible such that they can be useful individually
//! (e.g., applications that only need to specify parsing but not serialization, or vice versa). However,
//! Vest++ combinators generally provide trait implementations for all of these traits, and the proofs
//! in the [`proof`] module often rely on multiple, if not all, of these traits being implemented
//! for the combinators in question.
//!
//! ## [`proof`] — Proof Family of Traits
//!
//! - [`proof::SPRoundTrip`] — serialize-parse roundtrip
//! - [`proof::SPRoundTripDps`] — serialize-parse roundtrip (the DPS variant, used mostly internally)
//! - [`proof::PSRoundTrip`] — parse-serialize roundtrip
//! - [`proof::NonMalleable`] — parser non-malleability
//! - [`proof::NoLookAhead`] — parser no-look-ahead property
//! - [`proof::EquivSerializers`] / [`proof::EquivSerializersGeneral`] — DPS ↔ non-DPS equivalence
//!
//! Following the same philosophy as the specification traits, these proof traits are defined on top of
//! a *minimal* set of specification traits, and crutially, they are *not* defined/dependent on each other.
//! This way, combinators can implement only the proof traits that are relevant to their intended use cases
//! (e.g., formats that accept non-canonical encodings may not be non-malleable, and thus would not implement
//!  [`proof::NonMalleable`]).
//!
//! ## [`fns`] — Spec Function Combinators
//!
//! Type aliases and trait implementations that allow plain Verus `spec_fn`s
//! to be used as combinators without defining new types.

pub mod fns;
pub mod proof;
pub mod spec;
