pub mod proof;
pub mod spec;

use crate::core::spec::{SpecParser, SpecPred};
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

} // verus!
