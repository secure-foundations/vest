//! Combinators for composing binary data formats.
//!
//! Each format implements only the specification, proof, and executable traits
//! that its semantics justify. In particular, deliberately malleable formats
//! such as [`Alt`] and the permutation combinators do not claim
//! [`NonMalleable`](crate::core::proof::NonMalleable). See the
//! [combinator guide](https://secure-foundations.github.io/vest/guide/library/combinators.html)
//! for the overall construction model.
//!
//! # Primitive combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Fixed<N>`] | Exactly `N` bytes |
//! | [`Varied<Len>`] | Variable-length bytes determined by a length parameter |
//! | [`U8`] | Unsigned 8-bit integer |
//! | [`I8`] | Signed 8-bit integer |
//! | [`U16Le`] / [`U16Be`] | Unsigned 16-bit integer (little/big-endian) |
//! | [`I16Le`] / [`I16Be`] | Signed 16-bit integer (little/big-endian) |
//! | [`U24Le`] / [`U24Be`] | Unsigned 24-bit integer represented as `u32` (little/big-endian) |
//! | [`U32Le`] / [`U32Be`] | Unsigned 32-bit integer (little/big-endian) |
//! | [`I32Le`] / [`I32Be`] | Signed 32-bit integer (little/big-endian) |
//! | [`U64Le`] / [`U64Be`] | Unsigned 64-bit integer (little/big-endian) |
//! | [`I64Le`] / [`I64Be`] | Signed 64-bit integer (little/big-endian) |
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
//! | [`Preceded<A, AVal, B>`] | Same as `Pair(A, B)`, but discards A's value and uses `a_val` as its serialization witness |
//! | [`Terminated<A, B, BVal>`] | Same as `Pair(A, B)`, but discards B's value and uses `b_val` as its serialization witness |
//! | [`Permute2<P1, P2>`] | Accepts either order of two components, serializes the declared order (malleable) |
//! | [`Permute3<A, B, C>`] | Accepts any of the 6 orders of three components (malleable) |
//! | [`Permute4<A, B, C, D>`] | Accepts any of the 24 orders of four components (malleable) |
//! | [`Permute5<A, B, C, D, E>`] | Accepts any of the 120 orders of five components (malleable) |
//! | [`Mapped<Inner, M>`] | Isomorphic format transformation via a [bijection](mapped::spec::SpecMapper) |
//! | [`TryMap<Inner, M>`] | `Mapped` plus a parse-time `wf_in` check |
//! | [`Refined<Inner, Pred>`] | Format refinement via a [predicate](crate::core::spec::SpecPred) |
//! | [`Const<Inner, T>`] | Matches and returns a specific constant value |
//! | [`PrefixTagged<Tg, T, Of>`] | A format preceded by a tag value |
//! | [`SuffixTagged<Of, Tg, T>`] | A format followed by a tag value |
//! | [`Cond<Inner>`] | Boolean-gated combinator (most often used in branches of `Choice` / `Alt`) |
//! | [`Named<Inner>`] | Like `Inner`, but annotates runtime parse errors with a static format name |
//!
//! # Dependent combinators
//!
//! | Combinator | Description |
//! |---|---|
//! | [`Bind<A, B>`] | Like `Pair<A, B>`, but `B` can depend on `A`'s value |
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
//! | [`FixWith<LIMIT, Body, Param>`] | Bounded fixpoint for recursive formats; use `Param = ()` for context-free recursion |
pub mod bits;
pub mod bytes;
pub mod choice;
pub mod cond;
pub mod congruence;
pub mod disjoint;
pub mod implicit;
pub mod length;
pub mod mapped;
pub mod marker;
pub mod named;
pub mod opt;
pub mod permute;
pub mod preceded;
pub mod recursive;
pub mod reference;
pub mod refined;
pub mod sints;
pub mod star;
pub mod tail;
pub mod terminated;
pub mod tuple;
pub mod uints;

pub use bits::Bits;
pub use bytes::{AndThen, ExactLen, Fixed, Varied};
pub use choice::{Alt, Choice, Dispatch, Sum};
pub use cond::Cond;
pub use implicit::Implicit;
// Not part of the documented public API. These are still reachable because the `vest_dev`
// experiments depend on them; they are hidden so they do not appear in the published catalog.
#[doc(hidden)]
pub use implicit::{DepCombinator, KVFormat, TLVal, TVLeaf, TVOr, VoidTag};
pub use length::AsLen;
pub use mapped::{Mapped, TryMap};
pub use marker::{exec::ExecNever, Empty, Void};
pub use named::Named;
pub use opt::{Opt, Optional};
pub use permute::{Permute2, Permute3, Permute4, Permute5};
pub use preceded::Preceded;
pub use recursive::FixWith;
pub use reference::Ref;
pub use refined::{Const, PrefixTagged, Refined, SuffixTagged};
pub use sints::{I16Be, I16Le, I32Be, I32Le, I64Be, I64Le, I8};
pub use star::{Array, Repeat, RepeatN, Star};
pub use tail::{Eof, OptionalEnd, RepeatTillEnd, Tail};
pub use terminated::Terminated;
pub use tuple::{Bind, Pair};
pub use uints::{U16Be, U16Le, U24Be, U24Le, U32Be, U32Le, U64Be, U64Le, U8};
