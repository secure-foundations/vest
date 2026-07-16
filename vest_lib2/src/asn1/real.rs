//! ASN.1 DER REAL contents.
//!
//! REAL is represented by its canonical contents octets rather than by a machine
//! floating-point number. This exact representation covers arbitrary-size binary
//! mantissas and exponents, canonical decimal NR3, infinities, NaN, and minus zero
//! without rounding or special-value equality problems.
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

pub const ASCII_ZERO: u8 = 0x30;

pub const ASCII_ONE: u8 = 0x31;

pub const ASCII_NINE: u8 = 0x39;

pub const ASCII_MINUS: u8 = 0x2d;

pub const ASCII_PLUS: u8 = 0x2b;

pub const ASCII_FULL_STOP: u8 = 0x2e;

pub const ASCII_E: u8 = 0x45;

pub open spec fn ascii_digit(b: u8) -> bool {
    ASCII_ZERO <= b <= ASCII_NINE
}

pub open spec fn ascii_digits(bytes: Seq<u8>, start: int, end: int) -> bool {
    forall|i: int| #![auto] start <= i < end ==> ascii_digit(bytes[i])
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

pub open spec fn real_fmt() -> RealInnerFmt {
    Refined(Tail, |bytes: Seq<u8>| der_real_bytes_wf(bytes))
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

mod derived_specs {
    use super::*;

    impl SpecParser for RealFmt {
        type PVal = RealSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            real_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for RealFmt {
        type Val = RealSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            real_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for RealFmt {
        type SValue = RealSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            real_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for RealFmt {
        type SVal = RealSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            real_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for RealFmt {
        type T = RealSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            real_fmt().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl SafeParser for RealFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            real_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for RealFmt {
        open spec fn productive_inv(&self) -> bool {
            false
        }

        proof fn lemma_productive(&self, _ibuf: Seq<u8>) {
        }
    }

    impl SoundParser for RealFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            real_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            real_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for RealFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            real_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for RealFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            real_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for RealFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            real_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for RealFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            real_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

}

/// Borrowed, exact DER REAL contents.
pub struct Real<'a> {
    contents: &'a [u8],
}

impl<'a> DeepView for Real<'a> {
    type V = RealSpec;

    closed spec fn deep_view(&self) -> Self::V {
        self.contents.deep_view()
    }
}

impl<'a> Real<'a> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        der_real_bytes_wf(self.deep_view())
    }

    fn new_verified(contents: &'a [u8]) -> (value: Self)
        requires
            der_real_bytes_wf(contents@),
        ensures
            value.deep_view() == contents.deep_view(),
    {
        proof {
            assert(contents.deep_view() == contents@);
        }
        Self { contents }
    }

    /// Validates and borrows canonical DER REAL contents.
    pub fn from_der_contents(contents: &'a [u8]) -> (value: Result<Self, ParseError>)
        ensures
            value matches Ok(v) ==> v.deep_view() == contents.deep_view(),
            value is Ok <==> der_real_bytes_wf(contents@),
    {
        if der_real_bytes_wf_exec(contents) {
            Ok(Self::new_verified(contents))
        } else {
            Err(ParseError::non_canonical())
        }
    }

    pub fn contents(&self) -> &'a [u8] {
        self.contents
    }
}

impl<'a> Parser<&'a [u8]> for RealFmt {
    type PT = Real<'a>;

    fn parse(&self, ibuf: &&'a [u8]) -> PResult<Self::PT> {
        let (n, contents) = Tail.parse(ibuf)?;
        proof {
            contents.deep_view_eq_view();
        }
        if der_real_bytes_wf_exec(contents) {
            let value = Real::new_verified(contents);
            Ok((n, value))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<'a, Output: OutputBuf> Serializer<Output, Real<'a>> for RealFmt {
    fn serialize_into(&self, v: &Real<'a>, obuf: &mut Output) {
        proof {
            use_type_invariant(v);
        }
        Tail.serialize_into(&v.contents, obuf);
    }
}

impl<'a> Prepare<Real<'a>> for RealFmt {
    fn prepare(&self, v: &Real<'a>) -> Result<usize, PreSerializeError> {
        proof {
            use_type_invariant(v);
        }
        Tail.prepare(&v.contents)
    }
}

impl<'a> ByteLen<Real<'a>> for RealFmt {
    fn length(&self, v: &Real<'a>) -> usize {
        Tail.length(&v.contents)
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;
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
}
