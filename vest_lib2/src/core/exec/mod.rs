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

verus! {

#[verifier::external_body]
#[inline(always)]
pub fn cmp_byte_slices(a: &[u8], b: &[u8]) -> (r: bool)
    requires
        a.len() == b.len(),
    ensures
        r == (a@ == b@),
        r == (a.deep_view() == b.deep_view()),
{
    a == b
}

} // verus!
