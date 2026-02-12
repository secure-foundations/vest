pub mod proof;
pub mod spec;

use crate::core::spec::Consistency;
use vstd::prelude::*;

verus! {

/// Structured dependency used by [`Bind`].
///
/// The family of dependent combinators must be able to:
/// - build the dependent body combinator from a parsed key (`apply`)
/// - soundly *recover* the key from the body value during serialization (`recover`)
pub trait DepCombinator {
    type Key;

    type Val;

    type Body: Consistency<Val = Self::Val>;

    spec fn apply(&self, key: Self::Key) -> Self::Body;

    spec fn recover(&self, value: Self::Val) -> Self::Key;

    /// Recover must agree with any key that makes the body's value consistent.
    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val)
        ensures
            self.apply(key).consistent(value) ==> self.recover(value) == key,
    ;
}

/// The dependent combinator.
///
/// - parse: parse `Head` first to get a `key`, then apply `Tail::apply(key)` to get the `body`, returning only the body's parsed value
/// - serialize: recover a `key` from the value via `Tail::recover`, then serialize the `body` with that `key`, and finally serialize the `key`
pub struct Bind<Head, Tail>(pub Head, pub Tail);

/// Length dependency for `Varied` with a `u8` header length.
pub struct VariedU8;

/// Length dependency for `Varied` with a `u16` header length.
pub struct VariedU16;

/// Tagged-value idiom.
///
/// This supports n-ary tagged unions by chaining:
/// `TagVal(tag1, TagVal(tag2, TagValLeaf(tag3, C)))`
pub struct TVOr<Tag, C, Rest>(pub Tag, pub C, pub Rest);

/// Generic "impossible branch" for dependent tagged choices.
pub struct VoidTag<Tag>(pub core::marker::PhantomData<Tag>);

#[allow(non_snake_case)]
pub open spec fn Uninhabited<Tag>() -> VoidTag<Tag> {
    VoidTag(core::marker::PhantomData)
}

/// The TLV idiom that expects a `(tag, len)` header before the body, where the body is expected to be `len` bytes long.
pub struct TLVal<Tag, Body>(pub Body, pub core::marker::PhantomData<Tag>);

#[allow(non_snake_case)]
pub open spec fn TLV<Tag, Body>(body: Body) -> TLVal<Tag, Body> {
    TLVal(body, core::marker::PhantomData)
}
/// The tree version of [`TagVal`] for balanced choices.
pub struct TagValNode<Tag, Left, Right>(pub Left, pub Right, pub core::marker::PhantomData<Tag>);

/// Leaf for tagged union trees
pub struct TVLeaf<Tag, C>(pub Tag, pub C);

#[allow(non_snake_case)]
pub open spec fn TVNode<Tag, Left, Right>(left: Left, right: Right) -> TagValNode<
    Tag,
    Left,
    Right,
> {
    TagValNode(left, right, core::marker::PhantomData)
}


} // verus!
