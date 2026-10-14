//! ASN.1 NumericString contents.
//!
//! NumericString's character repertoire (space and decimal digits) is a strict
//! subset of PrintableString's repertoire, so its codec is a refinement of the
//! existing zero-copy PrintableString codec.
#[cfg(feature = "alloc")]
use super::PrintableStringOwned;
use super::{PrintableString, PrintableStringFmt, PrintableStringSpec};
use crate::combinators::Refined;
use crate::core::exec::fns::Pred;
use crate::core::spec::SpecPred;
use vstd::prelude::*;
#[cfg(not(feature = "alloc"))]
use vstd::string::StrSliceExecFns;

verus! {

pub type NumericString<'a> = PrintableString<'a>;

#[cfg(feature = "alloc")]
pub type NumericStringOwned = PrintableStringOwned;

pub type NumericStringSpec = PrintableStringSpec;

#[derive(Clone, Copy)]
pub struct NumericStringChars;

/// NumericString permits space and ASCII decimal digits.
#[verifier::allow_in_spec]
pub fn is_numeric_string_char(c: char) -> bool
    returns
        c == ' ' || ('0' <= c && c <= '9'),
{
    c == ' ' || ('0' <= c && c <= '9')
}

pub open spec fn is_valid_numeric_string(chars: Seq<char>) -> bool {
    forall|i: int| 0 <= i < chars.len() ==> is_numeric_string_char(#[trigger] chars[i])
}

impl SpecPred<PrintableStringSpec> for NumericStringChars {
    open spec fn apply(&self, value: PrintableStringSpec) -> bool {
        is_valid_numeric_string(value.inner)
    }
}

// vstd currently gates its `Chars` iterator contracts behind `alloc`, even
// though Rust's character iterator itself does not allocate.
#[cfg(feature = "alloc")]
fn check_numeric_chars(inner: &str) -> (valid: bool)
    ensures
        valid == is_valid_numeric_string(inner.deep_view()),
{
    inner.chars().all(
        |c: char| -> (valid: bool)
            ensures
                valid == is_numeric_string_char(c),
            { is_numeric_string_char(c) },
    )
}

#[cfg(not(feature = "alloc"))]
fn check_numeric_chars(inner: &str) -> (valid: bool)
    ensures
        valid == is_valid_numeric_string(inner.deep_view()),
{
    let len = inner.unicode_len();
    for i in 0..len
        invariant
            len == inner.deep_view().len(),
            forall|k: int| 0 <= k < i ==> is_numeric_string_char(#[trigger] inner.deep_view()[k]),
    {
        let c = inner.get_char(i);
        if !is_numeric_string_char(c) {
            assert(!is_numeric_string_char(inner.deep_view()[i as int]));
            return false;
        }
    }
    true
}

impl<'a> Pred<PrintableString<'a>> for NumericStringChars {
    fn test(&self, value: &PrintableString<'a>) -> (ok: bool) {
        check_numeric_chars(value.inner())
    }
}

#[cfg(feature = "alloc")]
impl Pred<PrintableStringOwned> for NumericStringChars {
    fn test(&self, value: &PrintableStringOwned) -> (ok: bool) {
        check_numeric_chars(value.inner())
    }
}

pub type NumericStringFmt = Refined<PrintableStringFmt, NumericStringChars>;

#[allow(non_upper_case_globals)]
pub const NumericStringFmt: NumericStringFmt = Refined(PrintableStringFmt, NumericStringChars);

} // verus!
