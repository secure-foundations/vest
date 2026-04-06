//! Dependent sequential combinators that omit the header value from the body and recover it during serialization.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::Consistency;
use vstd::prelude::*;

verus! {

/// A family of dependent combinators indexed by a key type.
///
/// Used to constrain the `Tail` combinator in a [`Implicit<Head, Tail>`].
///
/// While possible, most users will use the provided dependent combinators ([`TVOr`], [`TLVal`],
/// [`VariedLen`], etc.) rather than implementing this trait directly.
pub trait DepCombinator {
    /// The type of keys parsed by the head combinator/to be recovered during serialization.
    type Key;

    /// The type of values consumed/produced by the body combinator.
    type Val;

    /// The type of the body combinator produced by `apply`.
    type Body: Consistency<Val = Self::Val>;

    /// Given a key, produce the body combinator for that key.
    spec fn apply(&self, key: Self::Key) -> Self::Body;

    /// Given a body value, recover the key used to produce the body combinator.
    spec fn recover(&self, value: Self::Val) -> Self::Key;

    /// Recover must agree with any key that makes the body's value consistent.
    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val)
        ensures
            self.apply(key).consistent(value) ==> self.recover(value) == key,
    ;
}

/// Dependent sequential combinator with deterministic key recovery.
///
/// Parsing semantics: parse `Head` to get a key, then parse the
/// body via `Tail::apply(key)`. Only the body value is returned.
///
/// The key is recovered via `Tail::recover(value)` during serialization.
///
/// ## Consistency
///
/// A value `v: Tail::Val` is consistent with `Implicit(Head, Tail)` iff
/// ```rust
/// let key = self.1.recover(v);
/// self.0.consistent(key) && self.1.apply(key).consistent(v)
/// ```
///
/// ## Unambiguity
///
/// ```rust
/// self.0.unambiguous() &&
/// forall|key: Head::PVal| #[trigger] (self.1.apply(key)).unambiguous()
/// ```
pub struct Implicit<Head, Tail>(pub Head, pub Tail);

/// One of the [dependent family of combinators](DepCombinator)
///
/// Typically used as `Implicit(U8, VLData())`.
pub struct VariedLen<Len>(pub core::marker::PhantomData<Len>);

/// Convenience constructor for [`VariedLen`].
#[allow(non_snake_case)]
pub open spec fn VLData<Len>() -> VariedLen<Len> {
    VariedLen(core::marker::PhantomData)
}

/// One of the [dependent family of combinators](DepCombinator)
///
/// Typically used as `Implicit(U16Le, VLDataOf(inner_fmt))`.
pub struct VariedLenOf<Len, Then>(pub core::marker::PhantomData<Len>, pub Then);

/// Convenience constructor for [`VariedLenOf`].
#[allow(non_snake_case)]
pub open spec fn VLDataOf<Len, C>(c: C) -> VariedLenOf<Len, C> {
    VariedLenOf(core::marker::PhantomData, c)
}

/// One of the [dependent family of combinators](DepCombinator)
///
/// Typically used to build linear chains of tagged unions: `TVOr(0x01u8, fmt1, TVOr(0x02u8, fmt2, Uninhabited()))`
pub struct TVOr<Tag, C, Rest>(pub Tag, pub C, pub Rest);

/// One of the [dependent family of combinators](DepCombinator)
///
/// Typically used in the "uninhabited" branch of a [`TVOr`] chain.
pub struct VoidTag<Tag>(pub core::marker::PhantomData<Tag>);

/// Convenience constructor for [`VoidTag`].
#[allow(non_snake_case)]
pub open spec fn Uninhabited<Tag>() -> VoidTag<Tag> {
    VoidTag(core::marker::PhantomData)
}

/// One of the [dependent family of combinators](DepCombinator)
///
/// Typically used as `Implicit((U8, U16Le), TLVOf(body))`.
pub struct TLVal<Tag, Len, Body>(pub Body, pub core::marker::PhantomData<(Tag, Len)>);

/// Convenience constructor for [`TLVal`].
#[allow(non_snake_case)]
pub open spec fn TLVOf<Tag, Len, Body>(body: Body) -> TLVal<Tag, Len, Body> {
    TLVal(body, core::marker::PhantomData)
}

/// One of the [dependent family of combinators](DepCombinator)
///
/// Balanced binary tree node for tag-value choices.
pub struct TagValNode<Tag, Left, Right>(pub Left, pub Right, pub core::marker::PhantomData<Tag>);

/// One of the [dependent family of combinators](DepCombinator)
///
/// Leaf node for tag-value tree.
pub struct TVLeaf<Tag, C>(pub Tag, pub C);

/// Convenience constructor for [`TagValNode`].
#[allow(non_snake_case)]
pub open spec fn TVNode<Tag, Left, Right>(left: Left, right: Right) -> TagValNode<
    Tag,
    Left,
    Right,
> {
    TagValNode(left, right, core::marker::PhantomData)
}

/// Dependent sequential combinator with explicit recovery function.
pub struct ImplicitManual<A, B, Recover>(pub A, pub B, pub Recover);

} // verus!
