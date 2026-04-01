//! Combinators for composing binary data formats.
//!
//! # Primitive combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Fixed<N>`] | Exactly `N` bytes |
//! | [`Varied<Len>`] | Variable-length bytes determined by a length parameter |
//! | [`U8`] | Unsigned 8-bit integer |
//! | [`U16Le`] / [`U16Be`] | Unsigned 16-bit integer (little/big-endian) |
//! | [`U32Le`] / [`U32Be`] | Unsigned 32-bit integer (little/big-endian) |
//!
//! # Higher-order combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Pair<A, B>`] | Sequential composition |
//! | [`Choice<A, B>`] | Non-malleable ordered alternative |
//! | [`Alt<A, B>`] | Malleable ordered alternative |
//! | [`Opt<A>`] | Optional value |
//! | [`Optional<A, B>`] | Same as `Pair(Opt<A>, B)`, but disambiguates `A` and `B` |
//! | [`Star<A>`] | The Kleene star: zero-or-more repetitions |
//! | [`Repeat<A, B>`] | Same as `Pair(Star<A>, B)`, but disambiguates `A` and `B` |
//! | [`RepeatN<C, Len>`] | Fixed number of repetitions determined by a length parameter |
//! | [`Array<N, C>`] | Array of values of length `N` |
//! | [`Preceded<A, B>`] | Same as `Pair(A, B)`, but discards A's value |
//! | [`Terminated<A, B>`] | Same as `Pair(A, B)`, but discards B's value |
//! | [`Mapped<Inner, M>`] | Isomorphic format transformation via a [bijection](mapped::spec::Mapper) |
//! | [`Refined<Inner, Pred>`] | Format refinement via a [predicate](crate::core::spec::SpecPred) |
//! | [`Tag<Inner, T>`] | Matches a specific constant value |
//! | [`Tagged<T, Of>`] | Same as `Preceded<Tag<T, T::Val>, Of>` (for convenience) |
//! | [`Cond<Inner>`] | Boolean-gated combinator (most often used in branches of `Choice` / `Alt`) |
//!
//! # Dependent combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`DepPair<A, B>`] | Like `Pair<A, B>`, but `B` can depend on `A`'s value |
//! | [`Bind<A, B>`] | Like `Implicit<A, B>`, but `B` must be one of the [dependent family of combinators](DepCombinator) |
//!
//! ## Dependent family of combinators
//!
//! Each combinator in this family explicitly declares the value(s) it depends on during parsing, and provides a recovery function
//! to reconstruct those values during serialization (see [`DepCombinator`] for details).
//!
//! | Combinator | Dependency | Description |
//! |---|---|---|
//! | [`dependent::VLData<Len>`] | Any value that can be used [as a length parameter](AsLen) | Length-prefixed raw bytes |
//! | [`dependent::VLDataOf<Len, C>`] | Same as `VLData` | Length-prefixed bytes interpreted by format `C` |
//! | [`dependent::TVOr<Tag, C, Rest>`] | Any value that can be used as a tag | A chain of tagged unions |
//! | [`dependent::Uninhabited<Tag>`] | Any value | End of a tagged union chain |
//! | [`dependent::TLVOf<Tag, Len, Body>`] | A pair of `(Tag, Len)` | A TLV (tag-length-value) format |
//!
//! # Tail combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Tail`] | Like [`Varied`], but at the tail position (underspecify the format and allow trailing data) |
//! | [`Eof`] | Signals end-of-file (no trailing data) |
//! | [`OptionalEnd<C>`] | Same as `Optional<C, Eof>` (for convenience) |
//! | [`RepeatTillEnd<C>`] | Same as `Repeat<C, Eof>` (for convenience) |
//!
//! # Marker combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Empty`] | Unit (nothing interesting, but still occupies zero bytes) |
//! | [`Void`] | Bottom (no value can satisfy this format) |
//!
//! # Recursive combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Fix<LIMIT, Body>`] | (Compile-time) bounded fixpoint for recursive formats |
pub mod berbool;
pub mod bytes;
pub mod choice;
pub mod cond;
pub mod dependent;
pub mod disjoint;
pub mod implicit;
pub mod length;
pub mod mapped;
pub mod marker;
pub mod opt;
pub mod permute;
pub mod preceded;
pub mod recursive;
pub mod refined;
pub mod star;
pub mod tail;
pub mod terminated;
pub mod tuple;
pub mod uints;

pub use berbool::BerBool;
pub use bytes::{Fixed, Varied};
pub use choice::{Alt, Choice, Sum};
pub use cond::Cond;
pub use dependent::{Bind, DepCombinator, TVLeaf, TVOr, VoidTag};
pub use implicit::{DepPair, ImplicitAuto};
pub use length::AsLen;
pub use mapped::Mapped;
pub use marker::{Empty, Void};
pub use opt::{Opt, Optional};
pub use permute::{Permute2, Permute3, Permute4};
pub use preceded::Preceded;
// pub use recursive::{
//     Fix, GoodRecSBody, NonMalleableRecPBody, NonTailRecSBodyDPS, RecBLenBody, RecCnstcyBody,
//     RecPBody, RecSBody, RecSBodyDPS, SoundRecPBody,
// };
pub use refined::{Refined, Tag, Tagged};
pub use star::{Array, Repeat, RepeatN, Star};
pub use tail::{Eof, OptionalEnd, RepeatTillEnd, Tail};
pub use terminated::Terminated;
pub use tuple::Pair;
pub use uints::{U16Be, U16Le, U32Be, U32Le, U8};
