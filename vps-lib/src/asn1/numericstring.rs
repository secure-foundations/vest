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
use vstd::string::StrSliceExecFns;

verus! {

pub type NumericString<'a> = PrintableString<'a>;

#[cfg(feature = "alloc")]
pub type NumericStringOwned = PrintableStringOwned;

pub type NumericStringSpec = PrintableStringSpec;

#[derive(Clone, Copy)]
pub struct NumericStringChars;

pub open spec fn is_numeric_string_char(c: char) -> bool {
    c as u32 == 0x20 || (0x30 <= c as u32 && c as u32 <= 0x39)
}

pub open spec fn is_valid_numeric_string(chars: Seq<char>) -> bool {
    forall|i: int| 0 <= i < chars.len() ==> is_numeric_string_char(#[trigger] chars[i])
}

impl SpecPred<PrintableStringSpec> for NumericStringChars {
    open spec fn apply(&self, value: PrintableStringSpec) -> bool {
        is_valid_numeric_string(value.inner)
    }
}

impl<'a> Pred<PrintableString<'a>> for NumericStringChars {
    fn test(&self, value: &PrintableString<'a>) -> (ok: bool) {
        let inner = value.inner();
        let len = inner.unicode_len();
        for i in 0..len
            invariant
                len == inner.deep_view().len(),
                inner.deep_view() == value.deep_view().inner,
                forall|k: int|
                    0 <= k < i ==> is_numeric_string_char(#[trigger] inner.deep_view()[k]),
        {
            let c = inner.get_char(i);
            let code = c as u32;
            if !(code == 0x20 || (0x30 <= code && code <= 0x39)) {
                assert(!is_numeric_string_char(inner.deep_view()[i as int]));
                return false;
            }
        }
        true
    }
}

#[cfg(feature = "alloc")]
impl Pred<PrintableStringOwned> for NumericStringChars {
    fn test(&self, value: &PrintableStringOwned) -> (ok: bool) {
        let inner = value.inner();
        let len = inner.unicode_len();
        for i in 0..len
            invariant
                len == inner.deep_view().len(),
                inner.deep_view() == value.deep_view().inner,
                forall|k: int|
                    0 <= k < i ==> is_numeric_string_char(#[trigger] inner.deep_view()[k]),
        {
            let c = inner.get_char(i);
            let code = c as u32;
            if !(code == 0x20 || (0x30 <= code && code <= 0x39)) {
                assert(!is_numeric_string_char(inner.deep_view()[i as int]));
                return false;
            }
        }
        true
    }
}

pub type NumericStringFmt = Refined<PrintableStringFmt, NumericStringChars>;

#[allow(non_upper_case_globals)]
pub const NumericStringFmt: NumericStringFmt = Refined(PrintableStringFmt, NumericStringChars);

} // verus!
