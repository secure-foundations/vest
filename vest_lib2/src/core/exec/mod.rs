//! Executable parsing and serialization.
pub mod error;
pub mod fns;
pub mod input;
pub mod parser;
pub mod serializer;

pub use error::{ParseError, ParseErrorKind};
pub use parser::{PResult, Parser};
pub use serializer::{ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer};

use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqIs;

verus! {

pub assume_specification<T: std::cmp::PartialEq<U>, U>[ <[T] as PartialEq<[U]>>::eq ](
    x: &[T],
    y: &[U],
) -> (res: bool)
    ensures
        res == (x@.len() == y@.len() && forall|i: int|
            #![auto]
            0 <= i < x@.len() ==> x@[i].is_eq(&y@[i])),
;

#[inline(always)]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
        r == (a.deep_view() == b.deep_view()),
{
    let res = *a == *b;
    assert(a@ == a.deep_view());
    assert(b@ == b.deep_view());
    assert(res ==> (a.deep_view() == b.deep_view()));
    res
}

} // verus!
