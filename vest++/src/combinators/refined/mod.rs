pub mod proof;
pub mod spec;

use crate::core::spec::SpecByteLen;
use vstd::prelude::*;

verus! {

pub struct Refined<Inner, Pred> {
    pub inner: Inner,
    pub pred: Pred,
}

pub struct Tag<Inner, Tag> {
    pub inner: Inner,
    pub tag: Tag,
}

pub struct Tagged<Tag: SpecByteLen, Of>(pub Tag, pub Tag::T, pub Of);

} // verus!
