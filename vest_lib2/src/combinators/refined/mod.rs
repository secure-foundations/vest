//! Value refinement and constant-value combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::SpecByteLen;
use vstd::prelude::*;

use super::{Preceded, Terminated};

verus! {

/// Value refinement combinator: filters values through a predicate.
///
/// ## Consistency
///
/// `inner.consistent(v) && predicate.apply(v)`.
#[derive(Copy)]
pub struct Refined<Inner, Predicate>(pub Inner, pub Predicate);

impl<Inner: Clone, Predicate: Clone> Clone for Refined<Inner, Predicate> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.0,), cloned.0),
            call_ensures(Predicate::clone, (&self.1,), cloned.1),
    {
        Refined(self.0.clone(), self.1.clone())
    }
}

/// Constant-value combinator: matches a specific constant value.
///
/// Parsing semantics: parses with `inner` and succeeds only if the result equals the expected value.
/// The matched constant value itself is returned.
///
/// Implements [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal).
#[derive(Copy)]
pub struct Const<Inner, Value>(pub Inner, pub Value);

impl<Inner: Clone, Value: Clone> Clone for Const<Inner, Value> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.0,), cloned.0),
            call_ensures(Value::clone, (&self.1,), cloned.1),
    {
        Const(self.0.clone(), self.1.clone())
    }
}

#[allow(type_alias_bounds)]
pub type PrefixTagged<TagFmt: SpecByteLen, Of, Tag = <TagFmt as SpecByteLen>::T> = Preceded<
    Const<TagFmt, Tag>,
    Tag,
    Of,
    false,
>;

#[allow(type_alias_bounds)]
pub type SuffixTagged<Of, TagFmt: SpecByteLen, Tag = <TagFmt as SpecByteLen>::T> = Terminated<
    Of,
    Const<TagFmt, Tag>,
    Tag,
    false,
>;

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn PrefixTagged<TagFmt, Of, Tag>(tag_fmt: TagFmt, tag: Tag, body: Of) -> PrefixTagged<
    TagFmt,
    Of,
    Tag,
> where TagFmt: SpecByteLen, Tag: Copy
    returns
        (Preceded::<Const<TagFmt, Tag>, Tag, Of, false> {
            a: Const(tag_fmt, tag),
            a_val: tag,
            b: body,
        }),
{
    let a = Const(tag_fmt, tag);
    let b = body;
    let a_val = tag;
    Preceded { a, a_val, b }
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn SuffixTagged<Of, TagFmt, Tag>(body: Of, tag_fmt: TagFmt, tag: Tag) -> SuffixTagged<
    Of,
    TagFmt,
    Tag,
> where TagFmt: SpecByteLen, Tag: Copy
    returns
        (Terminated::<Of, Const<TagFmt, Tag>, Tag, false> {
            a: body,
            b: Const(tag_fmt, tag),
            b_val: tag,
        }),
{
    let a = body;
    let b = Const(tag_fmt, tag);
    let b_val = tag;
    Terminated { a, b, b_val }
}

/// Sugar for `Preceded { a: Const(inner, tag), a_val: tag, b: body }`.
#[derive(Copy)]
pub struct WithPrefixTag<Tg: SpecByteLen, Of>(pub Tg, pub Tg::T, pub Of);

impl<Tg: SpecByteLen + Clone, Of: Clone> Clone for WithPrefixTag<Tg, Of> where Tg::T: Clone {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Tg::clone, (&self.0,), cloned.0),
            call_ensures(Tg::T::clone, (&self.1,), cloned.1),
            call_ensures(Of::clone, (&self.2,), cloned.2),
    {
        WithPrefixTag(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

/// Sugar for `Terminated { a: body, b: Const(inner, tag), b_val: tag }`.
#[derive(Copy)]
pub struct WithSuffixTag<Tg: SpecByteLen, Of>(pub Tg, pub Tg::T, pub Of);

impl<Tg: SpecByteLen + Clone, Of: Clone> Clone for WithSuffixTag<Tg, Of> where Tg::T: Clone {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Tg::clone, (&self.0,), cloned.0),
            call_ensures(Tg::T::clone, (&self.1,), cloned.1),
            call_ensures(Of::clone, (&self.2,), cloned.2),
    {
        WithSuffixTag(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

} // verus!
