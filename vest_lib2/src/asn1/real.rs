//! ASN.1 BER/DER REAL contents.
//!
//! REAL is represented by its exact contents octets rather than by a machine
//! floating-point number. This covers arbitrary-size binary mantissas and
//! exponents, ISO 6093 decimal forms, infinities, NaN, and minus zero without
//! rounding or special-value equality problems. DER restricts this representation
//! to the canonical subset required by X.690 section 11.3.
use crate::combinators::{Refined, Tail};
use crate::core::exec::input::InputSlice;
use crate::core::exec::output::OutputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::RealFmt;

verus! {

pub type RealSpec = Seq<u8>;

pub type RealInnerFmt = Refined<Tail, PredFnSpec<Seq<u8>>>;

pub const REAL_PLUS_INFINITY: u8 = 0x40;

pub const REAL_MINUS_INFINITY: u8 = 0x41;

pub const REAL_NOT_A_NUMBER: u8 = 0x42;

pub const REAL_MINUS_ZERO: u8 = 0x43;

pub const REAL_DECIMAL_NR3: u8 = 0x03;

pub const ASCII_SPACE: u8 = 0x20;

pub const ASCII_ZERO: u8 = 0x30;

pub const ASCII_ONE: u8 = 0x31;

pub const ASCII_NINE: u8 = 0x39;

pub const ASCII_MINUS: u8 = 0x2d;

pub const ASCII_PLUS: u8 = 0x2b;

pub const ASCII_FULL_STOP: u8 = 0x2e;

pub const ASCII_COMMA: u8 = 0x2c;

pub const ASCII_E: u8 = 0x45;

pub const ASCII_LOWER_E: u8 = 0x65;

pub open spec fn ascii_digit(b: u8) -> bool {
    ASCII_ZERO <= b <= ASCII_NINE
}

pub open spec fn ascii_nonzero_digit(b: u8) -> bool {
    ASCII_ONE <= b <= ASCII_NINE
}

pub open spec fn ascii_digits(bytes: Seq<u8>, start: int, end: int) -> bool {
    forall|i: int| #![auto] start <= i < end ==> ascii_digit(bytes[i])
}

pub open spec fn ascii_digits_have_nonzero(bytes: Seq<u8>, start: int, end: int) -> bool {
    exists|i: int| #![auto] start <= i < end && ascii_nonzero_digit(bytes[i])
}

pub open spec fn skip_ascii_spaces(bytes: Seq<u8>, start: nat) -> nat
    decreases bytes.len() - start,
{
    if start < bytes.len() && bytes[start as int] == ASCII_SPACE {
        skip_ascii_spaces(bytes, start + 1)
    } else {
        start
    }
}

pub open spec fn scan_ascii_digits(bytes: Seq<u8>, start: nat) -> nat
    decreases bytes.len() - start,
{
    if start < bytes.len() && ascii_digit(bytes[start as int]) {
        scan_ascii_digits(bytes, start + 1)
    } else {
        start
    }
}

pub open spec fn decimal_mark(b: u8) -> bool {
    b == ASCII_FULL_STOP || b == ASCII_COMMA
}

pub open spec fn exponent_mark(b: u8) -> bool {
    b == ASCII_E || b == ASCII_LOWER_E
}

pub open spec fn after_optional_sign(bytes: Seq<u8>, start: nat) -> nat {
    if start < bytes.len() && (bytes[start as int] == ASCII_PLUS || bytes[start as int]
        == ASCII_MINUS) {
        start + 1
    } else {
        start
    }
}

pub open spec fn ber_real_decimal_nr1_wf(bytes: Seq<u8>) -> bool {
    let start = after_optional_sign(bytes, skip_ascii_spaces(bytes, 1));
    let end = scan_ascii_digits(bytes, start);
    &&& start < end
    &&& end == bytes.len()
    &&& ascii_digits_have_nonzero(bytes, start as int, end as int)
}

pub open spec fn ber_real_decimal_significand(bytes: Seq<u8>) -> Option<(nat, nat, nat, nat)> {
    let before = after_optional_sign(bytes, skip_ascii_spaces(bytes, 1));
    let mark = scan_ascii_digits(bytes, before);
    if mark < bytes.len() && decimal_mark(bytes[mark as int]) {
        let after = mark + 1;
        let end = scan_ascii_digits(bytes, after);
        if before < mark || after < end {
            Some((before, mark, after, end))
        } else {
            None
        }
    } else {
        None
    }
}

pub open spec fn ber_real_decimal_mantissa_nonzero(
    bytes: Seq<u8>,
    before: nat,
    mark: nat,
    after: nat,
    end: nat,
) -> bool {
    ||| ascii_digits_have_nonzero(bytes, before as int, mark as int)
    ||| ascii_digits_have_nonzero(bytes, after as int, end as int)
}

pub open spec fn ber_real_decimal_nr2_wf(bytes: Seq<u8>) -> bool {
    match ber_real_decimal_significand(bytes) {
        Some((before, mark, after, end)) => {
            &&& end == bytes.len()
            &&& ber_real_decimal_mantissa_nonzero(bytes, before, mark, after, end)
        },
        None => false,
    }
}

pub open spec fn ber_real_decimal_nr3_wf(bytes: Seq<u8>) -> bool {
    match ber_real_decimal_significand(bytes) {
        Some((before, mark, after, end)) => {
            if end < bytes.len() && exponent_mark(bytes[end as int]) {
                let exponent_sign = end + 1;
                let exponent = exponent_sign + 1;
                let exponent_end = scan_ascii_digits(bytes, exponent);
                &&& exponent_sign < bytes.len()
                &&& (bytes[exponent_sign as int] == ASCII_PLUS || bytes[exponent_sign as int]
                    == ASCII_MINUS)
                &&& exponent < exponent_end
                &&& exponent_end == bytes.len()
                &&& ber_real_decimal_mantissa_nonzero(bytes, before, mark, after, end)
            } else {
                false
            }
        },
        None => false,
    }
}

/// BER decimal REAL contents using an ISO 6093 NR1, NR2, or NR3 field.
///
/// X.690 8.5.8 permits all three forms. Leading spaces and either case of the
/// exponent mark follow ISO 6093; NR2/NR3 require an explicit decimal mark and
/// NR3 requires a signed exponent. A decimal spelling of zero is rejected
/// because X.690 8.5.2 and 8.5.3 give zero dedicated encodings.
pub open spec fn ber_real_decimal_wf(bytes: Seq<u8>) -> bool {
    &&& bytes.len() > 1
    &&& match bytes[0] {
        0x01u8 => ber_real_decimal_nr1_wf(bytes),
        0x02u8 => ber_real_decimal_nr2_wf(bytes),
        0x03u8 => ber_real_decimal_nr3_wf(bytes),
        _ => false,
    }
}

pub open spec fn decimal_mantissa_start(bytes: Seq<u8>) -> int {
    if bytes.len() > 1 && bytes[1] == ASCII_MINUS {
        2
    } else {
        1
    }
}

/// Canonical X.690 DER NR3 at a proposed mantissa-terminating full stop.
pub open spec fn der_real_decimal_at(bytes: Seq<u8>, dot: int) -> bool {
    let start = decimal_mantissa_start(bytes);
    let exponent = dot + 2;
    &&& bytes.len() >= 6
    &&& bytes[0] == REAL_DECIMAL_NR3
    &&& start < dot < bytes.len()
    &&& ascii_digits(bytes, start, dot)
    &&& bytes[start] != ASCII_ZERO
    &&& bytes[dot - 1] != ASCII_ZERO
    &&& dot + 2 <= bytes.len()
    &&& bytes[dot] == ASCII_FULL_STOP
    &&& bytes[dot + 1] == ASCII_E
    &&& {
        // Exponent zero has the unique spelling "+0".
        ||| exponent + 2 == bytes.len() && bytes[exponent] == ASCII_PLUS && bytes[exponent + 1]
            == ASCII_ZERO
        // Every non-zero exponent omits PLUS, has an optional MINUS, and no
        // leading zero.
        ||| {
            let digits = if exponent < bytes.len() && bytes[exponent] == ASCII_MINUS {
                exponent + 1
            } else {
                exponent
            };
            &&& exponent < bytes.len()
            &&& bytes[exponent] != ASCII_PLUS
            &&& digits < bytes.len()
            &&& ASCII_ONE <= bytes[digits] <= ASCII_NINE
            &&& ascii_digits(bytes, digits, bytes.len() as int)
        }
    }
}

pub open spec fn der_real_decimal_wf(bytes: Seq<u8>) -> bool {
    exists|dot: int| der_real_decimal_at(bytes, dot)
}

pub open spec fn der_real_exponent_minimal(bytes: Seq<u8>, offset: int, len: int) -> bool {
    &&& len > 0
    &&& offset >= 0
    &&& offset + len <= bytes.len()
    &&& (len > 1 ==> {
        &&& !(bytes[offset] == 0x00u8 && bytes[offset + 1] < 0x80u8)
        &&& !(bytes[offset] == 0xffu8 && bytes[offset + 1] >= 0x80u8)
    })
}

/// Canonical DER binary REAL contents.
pub open spec fn der_real_binary_wf(bytes: Seq<u8>) -> bool {
    if bytes.len() < 3 {
        false
    } else {
        let info = bytes[0];
        let form = info & 0x03u8;
        let exponent_offset: int = if form == 0x03u8 {
            2
        } else {
            1
        };
        let exponent_len: int = match form {
            0x00u8 => 1,
            0x01u8 => 2,
            0x02u8 => 3,
            _ => bytes[1] as int,
        };
        let mantissa_offset = exponent_offset + exponent_len;
        &&& info & 0x80u8
            != 0
        // DER requires base 2 and a zero binary scaling factor.
        &&& info & 0x30u8 == 0
        &&& info & 0x0cu8
            == 0
        // The extended exponent-length form is canonical only when the three
        // compact forms are insufficient.
        &&& (form == 0x03u8 ==> exponent_len >= 4)
        &&& der_real_exponent_minimal(bytes, exponent_offset, exponent_len)
        &&& mantissa_offset
            < bytes.len()
        // M is unsigned, minimal, non-zero, and odd.
        &&& bytes[mantissa_offset] != 0
        &&& bytes.last() & 1u8 == 1u8
    }
}

/// BER binary REAL contents as specified by X.690 8.5.7.
pub open spec fn ber_real_binary_wf(bytes: Seq<u8>) -> bool {
    if bytes.len() < 3 {
        false
    } else {
        let info = bytes[0];
        let form = info & 0x03u8;
        let exponent_offset: int = if form == 0x03u8 {
            2
        } else {
            1
        };
        let exponent_len: int = match form {
            0x00u8 => 1,
            0x01u8 => 2,
            0x02u8 => 3,
            _ => bytes[1] as int,
        };
        let mantissa_offset = exponent_offset + exponent_len;
        &&& info & 0x80u8
            != 0
        // Base 2, 8, and 16 are valid; 0b11 is reserved.
        &&& info & 0x30u8
            != 0x30u8
        // The long exponent form has a non-zero length and X.690's
        // "first nine bits" minimality requirement.
        &&& (form == 0x03u8 ==> {
            &&& exponent_len > 0
            &&& der_real_exponent_minimal(bytes, exponent_offset, exponent_len)
        })
        &&& mantissa_offset
            < bytes.len()
        // N is a positive integer. BER permits redundant leading zero
        // octets and an unnormalized (even) mantissa.
        &&& exists|i: int| mantissa_offset <= i < bytes.len() && bytes[i] != 0u8
    }
}

pub open spec fn der_real_special_wf(bytes: Seq<u8>) -> bool {
    bytes.len() == 1 && (bytes[0] == REAL_PLUS_INFINITY || bytes[0] == REAL_MINUS_INFINITY
        || bytes[0] == REAL_NOT_A_NUMBER || bytes[0] == REAL_MINUS_ZERO)
}

/// Complete canonical DER predicate for REAL contents octets.
pub open spec fn der_real_bytes_wf(bytes: Seq<u8>) -> bool {
    ||| bytes.len() == 0  // positive zero
    ||| der_real_special_wf(bytes)
    ||| der_real_binary_wf(bytes)
    ||| der_real_decimal_wf(bytes)
}

/// Complete BER predicate for REAL contents octets.
pub open spec fn ber_real_bytes_wf(bytes: Seq<u8>) -> bool {
    ||| bytes.len() == 0  // positive zero
    ||| der_real_special_wf(bytes)
    ||| ber_real_binary_wf(bytes)
    ||| ber_real_decimal_wf(bytes)
}

pub open spec fn real_bytes_wf<const DER: bool>(bytes: Seq<u8>) -> bool {
    if DER {
        der_real_bytes_wf(bytes)
    } else {
        ber_real_bytes_wf(bytes)
    }
}

pub proof fn lemma_der_real_bytes_cases(bytes: Seq<u8>)
    ensures
        bytes.len() == 0 ==> der_real_bytes_wf(bytes),
        bytes.len() == 1 ==> (der_real_bytes_wf(bytes) <==> der_real_special_wf(bytes)),
        bytes.len() > 1 && bytes[0] & 0x80u8 != 0 ==> (der_real_bytes_wf(bytes)
            <==> der_real_binary_wf(bytes)),
        bytes.len() > 1 && bytes[0] & 0x80u8 == 0 && bytes[0] == REAL_DECIMAL_NR3 ==> (
        der_real_bytes_wf(bytes) <==> der_real_decimal_wf(bytes)),
        bytes.len() > 1 && bytes[0] & 0x80u8 == 0 && bytes[0] != REAL_DECIMAL_NR3
            ==> !der_real_bytes_wf(bytes),
{
    if bytes.len() > 1 && bytes[0] & 0x80u8 != 0 {
        if der_real_decimal_wf(bytes) {
            let dot = choose|dot: int| der_real_decimal_at(bytes, dot);
            assert(bytes[0] == REAL_DECIMAL_NR3);
            assert(REAL_DECIMAL_NR3 & 0x80u8 == 0) by (bit_vector);
        }
    }
}

pub proof fn lemma_ber_real_bytes_cases(bytes: Seq<u8>)
    ensures
        bytes.len() == 0 ==> ber_real_bytes_wf(bytes),
        bytes.len() == 1 ==> (ber_real_bytes_wf(bytes) <==> der_real_special_wf(bytes)),
        bytes.len() > 1 && bytes[0] & 0x80u8 != 0 ==> (ber_real_bytes_wf(bytes)
            <==> ber_real_binary_wf(bytes)),
        bytes.len() > 1 && bytes[0] & 0x80u8 == 0 ==> (ber_real_bytes_wf(bytes)
            <==> ber_real_decimal_wf(bytes)),
{
    if bytes.len() > 1 && bytes[0] & 0x80u8 != 0 {
        if ber_real_decimal_wf(bytes) {
            assert(bytes[0] == 0x01u8 || bytes[0] == 0x02u8 || bytes[0] == 0x03u8);
            assert(0x01u8 & 0x80u8 == 0 && 0x02u8 & 0x80u8 == 0 && 0x03u8 & 0x80u8 == 0)
                by (bit_vector);
        }
    }
}

pub open spec fn real_fmt<const DER: bool>() -> RealInnerFmt {
    Refined(Tail, |bytes: Seq<u8>| real_bytes_wf::<DER>(bytes))
}

pub proof fn lemma_decimal_dot_matches_scan(bytes: Seq<u8>, start: int, scanned: int, dot: int)
    requires
        start == decimal_mantissa_start(bytes),
        0 <= start <= scanned <= bytes.len(),
        ascii_digits(bytes, start, scanned),
        scanned == bytes.len() || !ascii_digit(bytes[scanned]),
        der_real_decimal_at(bytes, dot),
    ensures
        dot == scanned,
{
    if dot < scanned {
        assert(ascii_digit(bytes[dot]));
        assert(bytes[dot] == ASCII_FULL_STOP);
    } else if scanned < dot {
        assert(scanned < bytes.len());
        assert(ascii_digit(bytes[scanned]));
    }
}

pub proof fn lemma_decimal_scan_characterizes(bytes: Seq<u8>, start: int, scanned: int)
    requires
        start == decimal_mantissa_start(bytes),
        0 <= start <= scanned <= bytes.len(),
        ascii_digits(bytes, start, scanned),
        scanned == bytes.len() || !ascii_digit(bytes[scanned]),
    ensures
        der_real_decimal_wf(bytes) <==> der_real_decimal_at(bytes, scanned),
{
    if der_real_decimal_wf(bytes) {
        let dot = choose|dot: int| der_real_decimal_at(bytes, dot);
        lemma_decimal_dot_matches_scan(bytes, start, scanned, dot);
    }
}

fn all_ascii_digits(bytes: &[u8], start: usize, end: usize) -> (ok: bool)
    requires
        start <= end <= bytes@.len(),
    ensures
        ok == ascii_digits(bytes@, start as int, end as int),
{
    let mut i = start;
    while i < end
        invariant
            start <= i <= end <= bytes@.len(),
            ascii_digits(bytes@, start as int, i as int),
        decreases end - i,
    {
        if !(ASCII_ZERO <= bytes[i] && bytes[i] <= ASCII_NINE) {
            assert(!ascii_digits(bytes@, start as int, end as int));
            return false;
        }
        i += 1;
    }
    true
}

fn skip_ascii_spaces_exec(bytes: &[u8], start: usize) -> (end: usize)
    requires
        start <= bytes@.len(),
    ensures
        end == skip_ascii_spaces(bytes@, start as nat),
        start <= end <= bytes@.len(),
{
    let mut i = start;
    while i < bytes.len() && bytes[i] == ASCII_SPACE
        invariant
            start <= i <= bytes@.len(),
            skip_ascii_spaces(bytes@, start as nat) == skip_ascii_spaces(bytes@, i as nat),
        decreases bytes@.len() - i,
    {
        proof {
            reveal(skip_ascii_spaces);
            assert(skip_ascii_spaces(bytes@, i as nat) == skip_ascii_spaces(bytes@, i as nat + 1));
        }
        i += 1;
    }
    proof {
        reveal(skip_ascii_spaces);
        assert(skip_ascii_spaces(bytes@, i as nat) == i as nat);
    }
    i
}

fn scan_ascii_digits_exec(bytes: &[u8], start: usize) -> (end: usize)
    requires
        start <= bytes@.len(),
    ensures
        end == scan_ascii_digits(bytes@, start as nat),
        start <= end <= bytes@.len(),
        ascii_digits(bytes@, start as int, end as int),
        end == bytes@.len() || !ascii_digit(bytes@[end as int]),
{
    let mut i = start;
    while i < bytes.len() && ASCII_ZERO <= bytes[i] && bytes[i] <= ASCII_NINE
        invariant
            start <= i <= bytes@.len(),
            scan_ascii_digits(bytes@, start as nat) == scan_ascii_digits(bytes@, i as nat),
            ascii_digits(bytes@, start as int, i as int),
        decreases bytes@.len() - i,
    {
        proof {
            reveal(scan_ascii_digits);
            assert(scan_ascii_digits(bytes@, i as nat) == scan_ascii_digits(bytes@, i as nat + 1));
        }
        i += 1;
    }
    proof {
        reveal(scan_ascii_digits);
        assert(scan_ascii_digits(bytes@, i as nat) == i as nat);
    }
    i
}

fn ascii_digits_have_nonzero_exec(bytes: &[u8], start: usize, end: usize) -> (found: bool)
    requires
        start <= end <= bytes@.len(),
    ensures
        found == ascii_digits_have_nonzero(bytes@, start as int, end as int),
{
    let mut i = start;
    while i < end
        invariant
            start <= i <= end <= bytes@.len(),
            forall|j: int| #![auto] start <= j < i ==> !ascii_nonzero_digit(bytes@[j]),
        decreases end - i,
    {
        if ASCII_ONE <= bytes[i] && bytes[i] <= ASCII_NINE {
            assert(ascii_digits_have_nonzero(bytes@, start as int, end as int)) by {
                assert(ascii_nonzero_digit(bytes@[i as int]));
            }
            return true;
        }
        i += 1;
    }
    assert(!ascii_digits_have_nonzero(bytes@, start as int, end as int));
    false
}

fn ber_real_decimal_wf_exec(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == ber_real_decimal_wf(bytes@),
{
    if bytes.len() <= 1 {
        return false;
    }
    let representation = bytes[0];
    if representation != 0x01u8 && representation != 0x02u8 && representation != 0x03u8 {
        return false;
    }
    let mut start = skip_ascii_spaces_exec(bytes, 1);
    let ghost unsigned_start = start;
    if start < bytes.len() && (bytes[start] == ASCII_PLUS || bytes[start] == ASCII_MINUS) {
        start += 1;
    }
    assert(start as nat == after_optional_sign(bytes@, unsigned_start as nat));

    if representation == 0x01u8 {
        let end = scan_ascii_digits_exec(bytes, start);
        if start >= end || end != bytes.len() {
            return false;
        }
        return ascii_digits_have_nonzero_exec(bytes, start, end);
    }
    let mark = scan_ascii_digits_exec(bytes, start);
    if mark >= bytes.len() || !(bytes[mark] == ASCII_FULL_STOP || bytes[mark] == ASCII_COMMA) {
        return false;
    }
    let after = mark + 1;
    let end = scan_ascii_digits_exec(bytes, after);
    if start == mark && after == end {
        return false;
    }
    assert(ber_real_decimal_significand(bytes@) == Some(
        (start as nat, mark as nat, after as nat, end as nat),
    ));
    let before_nonzero = ascii_digits_have_nonzero_exec(bytes, start, mark);
    let after_nonzero = ascii_digits_have_nonzero_exec(bytes, after, end);
    let nonzero = before_nonzero || after_nonzero;

    if representation == 0x02u8 {
        return end == bytes.len() && nonzero;
    }
    if end >= bytes.len() || !(bytes[end] == ASCII_E || bytes[end] == ASCII_LOWER_E) {
        return false;
    }
    let exponent_sign = end + 1;
    if exponent_sign >= bytes.len() || !(bytes[exponent_sign] == ASCII_PLUS || bytes[exponent_sign]
        == ASCII_MINUS) {
        return false;
    }
    let exponent = exponent_sign + 1;
    let exponent_end = scan_ascii_digits_exec(bytes, exponent);
    exponent < exponent_end && exponent_end == bytes.len() && nonzero
}

fn scan_decimal_mantissa(bytes: &[u8], start: usize) -> (scanned: usize)
    requires
        start <= bytes@.len(),
    ensures
        start <= scanned <= bytes@.len(),
        ascii_digits(bytes@, start as int, scanned as int),
        scanned == bytes@.len() || !ascii_digit(bytes@[scanned as int]),
{
    let mut i = start;
    while i < bytes.len() && ASCII_ZERO <= bytes[i] && bytes[i] <= ASCII_NINE
        invariant
            start <= i <= bytes@.len(),
            ascii_digits(bytes@, start as int, i as int),
        decreases bytes@.len() - i,
    {
        i += 1;
    }
    i
}

fn der_real_decimal_at_exec(bytes: &[u8], dot: usize) -> (ok: bool)
    ensures
        ok == der_real_decimal_at(bytes@, dot as int),
{
    if bytes.len() < 6 || bytes[0] != REAL_DECIMAL_NR3 {
        return false;
    }
    let start = if bytes[1] == ASCII_MINUS {
        2
    } else {
        1
    };
    if start >= dot || dot >= bytes.len() {
        return false;
    }
    if !all_ascii_digits(bytes, start, dot) {
        return false;
    }
    if bytes[start] == ASCII_ZERO || bytes[dot - 1] == ASCII_ZERO {
        return false;
    }
    if dot > bytes.len() - 2 || bytes[dot] != ASCII_FULL_STOP || bytes[dot + 1] != ASCII_E {
        return false;
    }
    let exponent = dot + 2;
    if exponent <= bytes.len() - 2 && exponent + 2 == bytes.len() && bytes[exponent] == ASCII_PLUS
        && bytes[exponent + 1] == ASCII_ZERO {
        return true;
    }
    if exponent >= bytes.len() || bytes[exponent] == ASCII_PLUS {
        return false;
    }
    let digits = if bytes[exponent] == ASCII_MINUS {
        exponent + 1
    } else {
        exponent
    };
    if digits >= bytes.len() || bytes[digits] < ASCII_ONE || bytes[digits] > ASCII_NINE {
        return false;
    }
    all_ascii_digits(bytes, digits, bytes.len())
}

fn der_real_decimal_wf_exec(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == der_real_decimal_wf(bytes@),
{
    if bytes.len() < 2 || bytes[0] != REAL_DECIMAL_NR3 {
        return false;
    }
    let start = if bytes[1] == ASCII_MINUS {
        2
    } else {
        1
    };
    if start > bytes.len() {
        return false;
    }
    let scanned = scan_decimal_mantissa(bytes, start);
    let ok = der_real_decimal_at_exec(bytes, scanned);
    proof {
        assert(start as int == decimal_mantissa_start(bytes@));
        lemma_decimal_scan_characterizes(bytes@, start as int, scanned as int);
    }
    ok
}

fn der_real_binary_wf_exec(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == der_real_binary_wf(bytes@),
{
    if bytes.len() < 3 {
        return false;
    }
    let info = bytes[0];
    if info & 0x80u8 == 0 || info & 0x30u8 != 0 || info & 0x0cu8 != 0 {
        return false;
    }
    let form = info & 0x03u8;
    let exponent_offset = if form == 0x03u8 {
        2usize
    } else {
        1usize
    };
    let exponent_len = if form == 0x00u8 {
        1usize
    } else if form == 0x01u8 {
        2usize
    } else if form == 0x02u8 {
        3usize
    } else {
        bytes[1] as usize
    };
    let ghost spec_exponent_offset: int = if form == 0x03u8 {
        2
    } else {
        1
    };
    let ghost spec_exponent_len: int = match form {
        0x00u8 => 1,
        0x01u8 => 2,
        0x02u8 => 3,
        _ => bytes@[1] as int,
    };
    proof {
        assert(exponent_offset as int == spec_exponent_offset);
        assert(exponent_len as int == spec_exponent_len);
    }
    if form == 0x03u8 && exponent_len < 4 {
        return false;
    }
    if exponent_len == 0 || exponent_offset > bytes.len() || exponent_len > bytes.len()
        - exponent_offset {
        return false;
    }
    if exponent_len > 1 {
        let first = bytes[exponent_offset];
        let second = bytes[exponent_offset + 1];
        if (first == 0x00 && second < 0x80) || (first == 0xff && second >= 0x80) {
            proof {
                assert(!der_real_exponent_minimal(bytes@, spec_exponent_offset, spec_exponent_len));
                assert(!der_real_binary_wf(bytes@));
            }
            return false;
        }
    }
    let mantissa_offset = exponent_offset + exponent_len;
    proof {
        assert(mantissa_offset as int == spec_exponent_offset + spec_exponent_len);
    }
    if mantissa_offset >= bytes.len() || bytes[mantissa_offset] == 0 {
        proof {
            assert(!der_real_binary_wf(bytes@));
        }
        return false;
    }
    bytes[bytes.len() - 1] & 1u8 == 1u8
}

fn has_nonzero_octet(bytes: &[u8], start: usize) -> (found: bool)
    requires
        start <= bytes@.len(),
    ensures
        found == exists|i: int| start <= i < bytes@.len() && bytes@[i] != 0u8,
{
    let mut i = start;
    while i < bytes.len()
        invariant
            start <= i <= bytes@.len(),
            forall|j: int| start <= j < i ==> bytes@[j] == 0u8,
        decreases bytes@.len() - i,
    {
        if bytes[i] != 0 {
            assert(exists|j: int| start <= j < bytes@.len() && bytes@[j] != 0u8);
            return true;
        }
        i += 1;
    }
    assert(!(exists|j: int| start <= j < bytes@.len() && bytes@[j] != 0u8));
    false
}

fn ber_real_binary_wf_exec(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == ber_real_binary_wf(bytes@),
{
    if bytes.len() < 3 {
        return false;
    }
    let info = bytes[0];
    if info & 0x80u8 == 0 || info & 0x30u8 == 0x30u8 {
        return false;
    }
    let form = info & 0x03u8;
    let exponent_offset = if form == 0x03u8 {
        2usize
    } else {
        1usize
    };
    let exponent_len = if form == 0x00u8 {
        1usize
    } else if form == 0x01u8 {
        2usize
    } else if form == 0x02u8 {
        3usize
    } else {
        bytes[1] as usize
    };
    let ghost spec_exponent_offset: int = if form == 0x03u8 {
        2
    } else {
        1
    };
    let ghost spec_exponent_len: int = match form {
        0x00u8 => 1,
        0x01u8 => 2,
        0x02u8 => 3,
        _ => bytes@[1] as int,
    };
    proof {
        assert(exponent_offset as int == spec_exponent_offset);
        assert(exponent_len as int == spec_exponent_len);
    }

    if form == 0x03u8 && exponent_len == 0 {
        assert(!ber_real_binary_wf(bytes@));
        return false;
    }
    if exponent_offset > bytes.len() || exponent_len > bytes.len() - exponent_offset {
        proof {
            if exponent_offset > bytes@.len() {
                assert(spec_exponent_offset > bytes@.len());
            } else if exponent_len > bytes.len() - exponent_offset {
                assert(spec_exponent_offset + spec_exponent_len > bytes@.len());
            }
            assert(!ber_real_binary_wf(bytes@));
        }
        return false;
    }
    if form == 0x03u8 && exponent_len > 1 {
        let first = bytes[exponent_offset];
        let second = bytes[exponent_offset + 1];
        if (first == 0x00 && second < 0x80) || (first == 0xff && second >= 0x80) {
            proof {
                assert(!der_real_exponent_minimal(bytes@, spec_exponent_offset, spec_exponent_len));
            }
            return false;
        }
    }
    let mantissa_offset = exponent_offset + exponent_len;
    proof {
        assert(mantissa_offset as int == spec_exponent_offset + spec_exponent_len);
    }
    if mantissa_offset >= bytes.len() {
        return false;
    }
    has_nonzero_octet(bytes, mantissa_offset)
}

/// Executable checker for all canonical DER REAL contents forms.
pub fn der_real_bytes_wf_exec(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == der_real_bytes_wf(bytes@),
{
    proof {
        lemma_der_real_bytes_cases(bytes@);
    }
    if bytes.len() == 0 {
        true
    } else if bytes.len() == 1 {
        matches!(
            bytes[0],
            REAL_PLUS_INFINITY | REAL_MINUS_INFINITY | REAL_NOT_A_NUMBER | REAL_MINUS_ZERO
        )
    } else if bytes[0] & 0x80u8 != 0 {
        der_real_binary_wf_exec(bytes)
    } else if bytes[0] == REAL_DECIMAL_NR3 {
        der_real_decimal_wf_exec(bytes)
    } else {
        false
    }
}

/// Executable checker for all BER REAL contents forms.
pub fn ber_real_bytes_wf_exec(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == ber_real_bytes_wf(bytes@),
{
    proof {
        lemma_ber_real_bytes_cases(bytes@);
    }
    if bytes.len() == 0 {
        true
    } else if bytes.len() == 1 {
        matches!(
            bytes[0],
            REAL_PLUS_INFINITY | REAL_MINUS_INFINITY | REAL_NOT_A_NUMBER | REAL_MINUS_ZERO
        )
    } else if bytes[0] & 0x80u8 != 0 {
        ber_real_binary_wf_exec(bytes)
    } else {
        ber_real_decimal_wf_exec(bytes)
    }
}

pub fn real_bytes_wf_exec<const DER: bool>(bytes: &[u8]) -> (ok: bool)
    ensures
        ok == real_bytes_wf::<DER>(bytes@),
{
    if DER {
        der_real_bytes_wf_exec(bytes)
    } else {
        ber_real_bytes_wf_exec(bytes)
    }
}

mod derived_specs {
    use super::*;

    impl<const DER: bool> SpecParser for RealFmt<DER> {
        type PVal = RealSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            real_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for RealFmt<DER> {
        type Val = RealSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            real_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for RealFmt<DER> {
        type SValue = RealSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            real_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for RealFmt<DER> {
        type SVal = RealSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            real_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for RealFmt<DER> {
        type T = RealSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            real_fmt::<DER>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const DER: bool> SafeParser for RealFmt<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            real_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for RealFmt<DER> {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, _ibuf: Seq<u8>) {
        }
    }

    impl<const DER: bool> SoundParser for RealFmt<DER> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            real_fmt::<DER>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            real_fmt::<DER>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> GoodSerializer for RealFmt<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            real_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for RealFmt<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            real_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NonMalleable for RealFmt<DER> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            real_fmt::<DER>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializers for RealFmt<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            real_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

/// Borrowed, exact BER/DER REAL contents.
pub struct Real<'a, const DER: bool = true> {
    contents: &'a [u8],
}

impl<'a, const DER: bool> DeepView for Real<'a, DER> {
    type V = RealSpec;

    closed spec fn deep_view(&self) -> Self::V {
        self.contents.deep_view()
    }
}

impl<'a, const DER: bool> Real<'a, DER> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        real_bytes_wf::<DER>(self.deep_view())
    }

    fn new_verified(contents: &'a [u8]) -> (value: Self)
        requires
            real_bytes_wf::<DER>(contents@),
        ensures
            value.deep_view() == contents.deep_view(),
    {
        proof {
            assert(contents.deep_view() == contents@);
        }
        Self { contents }
    }

    /// Validates and borrows REAL contents under this format's encoding rules.
    pub fn from_contents(contents: &'a [u8]) -> (value: Result<Self, ParseError>)
        ensures
            value matches Ok(v) ==> v.deep_view() == contents.deep_view(),
            value is Ok <==> real_bytes_wf::<DER>(contents@),
    {
        if real_bytes_wf_exec::<DER>(contents) {
            Ok(Self::new_verified(contents))
        } else {
            Err(ParseError::non_canonical())
        }
    }

    pub fn contents(&self) -> (contents: &'a [u8])
        ensures
            contents.deep_view() == self.deep_view(),
    {
        self.contents
    }
}

impl<'a> Real<'a, true> {
    /// Validates and borrows canonical DER REAL contents.
    pub fn from_der_contents(contents: &'a [u8]) -> (value: Result<Self, ParseError>)
        ensures
            value matches Ok(v) ==> v.deep_view() == contents.deep_view(),
            value is Ok <==> der_real_bytes_wf(contents@),
    {
        Self::from_contents(contents)
    }
}

impl<'a> Real<'a, false> {
    /// Validates and borrows any well-formed BER REAL contents.
    pub fn from_ber_contents(contents: &'a [u8]) -> (value: Result<Self, ParseError>)
        ensures
            value matches Ok(v) ==> v.deep_view() == contents.deep_view(),
            value is Ok <==> ber_real_bytes_wf(contents@),
    {
        Self::from_contents(contents)
    }
}

impl<'a, const DER: bool> Parser<&'a [u8]> for RealFmt<DER> {
    type PT = Real<'a, DER>;

    fn parse(&self, ibuf: &&'a [u8]) -> PResult<Self::PT> {
        let (n, contents) = Tail.parse(ibuf)?;
        proof {
            contents.deep_view_eq_view();
        }
        if real_bytes_wf_exec::<DER>(contents) {
            let value = Real::new_verified(contents);
            Ok((n, value))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<'a, Output: OutputBuf, const DER: bool> Serializer<Output, Real<'a, DER>> for RealFmt<DER> {
    fn serialize_into(&self, v: &Real<'a, DER>, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        Tail.serialize_into(&v.contents, obuf);
    }
}

impl<'a, const DER: bool> Prepare<Real<'a, DER>> for RealFmt<DER> {
    fn prepare(&self, v: &Real<'a, DER>) -> Result<usize, PreSerializeError> {
        proof {
            use_type_invariant(v);
        }
        Tail.prepare(&v.contents)
    }
}

impl<'a, const DER: bool> ByteLen<Real<'a, DER>> for RealFmt<DER> {
    fn length(&self, v: &Real<'a, DER>) -> usize {
        Tail.length(&v.contents)
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;
    use crate::asn1::ber::REAL as BER_REAL;
    use crate::asn1::der::REAL;
    use crate::core::exec::{Parser, Prepare, SerializerExt};

    fn roundtrip(contents: &[u8]) {
        let mut input = vec![0x09, contents.len() as u8];
        input.extend_from_slice(contents);
        let (_, value) = REAL.parse(&&input[..]).unwrap();
        let mut output = vec![0; REAL.prepare(&value).unwrap()];
        REAL.serialize(&value, &mut output);
        assert_eq!(output, input);
    }

    fn roundtrip_ber(contents: &[u8]) {
        let mut input = vec![0x09, contents.len() as u8];
        input.extend_from_slice(contents);
        let (_, value) = BER_REAL.parse(&&input[..]).unwrap();
        let mut output = vec![0; BER_REAL.prepare(&value).unwrap()];
        BER_REAL.serialize(&value, &mut output);
        assert_eq!(output, input);
    }

    #[test]
    fn real_roundtrips_all_der_families() {
        roundtrip(&[]); // +0
        roundtrip(&[REAL_MINUS_ZERO]);
        roundtrip(&[REAL_PLUS_INFINITY]);
        roundtrip(&[REAL_MINUS_INFINITY]);
        roundtrip(&[REAL_NOT_A_NUMBER]);
        roundtrip(&[0x80, 0x00, 0x01]); // 1 * 2^0
        roundtrip(b"\x03123.E-2");
        roundtrip(b"\x031.E+0");
    }

    #[test]
    fn real_rejects_noncanonical_forms() {
        for contents in [
            &b"\x031.0E+0"[..],        // mantissa ends in zero
            &b"\x031.E+1"[..],         // plus is forbidden for non-zero exponent
            &[0x80, 0x00, 0x02],       // even mantissa
            &[0x83, 0x01, 0x00, 0x01], // long exponent form used for one octet
        ] {
            let mut input = vec![0x09, contents.len() as u8];
            input.extend_from_slice(contents);
            assert!(REAL.parse(&&input[..]).is_err());
        }
    }

    #[test]
    fn ber_real_roundtrips_additional_binary_and_decimal_forms() {
        roundtrip_ber(&[0x90, 0x00, 0x02]); // base 8, unnormalized mantissa
        roundtrip_ber(&[0x84, 0x00, 0x02]); // binary scale factor 1
        roundtrip_ber(&[0x83, 0x01, 0x00, 0x02]); // one-octet long exponent
        roundtrip_ber(b"\x01123"); // ISO 6093 NR1
        roundtrip_ber(b"\x02-12.5"); // ISO 6093 NR2
        roundtrip_ber(b"\x03 1.25E+2"); // ISO 6093 NR3
        roundtrip_ber(b"\x03.125e+3"); // no digit left of the decimal mark
    }

    #[test]
    fn ber_real_rejects_reserved_or_non_real_contents() {
        for contents in [
            &[0xb0, 0x00, 0x01][..], // reserved binary base
            &[0x80, 0x00, 0x00],     // zero binary mantissa
            &b"\x010"[..],           // plus zero must have empty contents
            &b"\x0212"[..],          // NR2 requires a decimal mark
            &b"\x031.2E2"[..],       // NR3 exponent sign is mandatory
        ] {
            let mut input = vec![0x09, contents.len() as u8];
            input.extend_from_slice(contents);
            assert!(BER_REAL.parse(&&input[..]).is_err());
        }
    }
}
