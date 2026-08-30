use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::{
    combinators::{mapped::spec::FnSpecMapper, Mapped, Refined, Tail},
    core::{proof::*, spec::*},
};
use vstd::assert_seqs_equal;
use vstd::prelude::*;
use OutputBuf;

use super::datetime::*;

verus! {

/// ASCII code for '+'
pub const ASCII_PLUS: u8 = 0x2b;

/// ASCII code for '-'
pub const ASCII_MINUS: u8 = 0x2d;

/// ASCII code for 'Z'
pub const ASCII_Z: u8 = 0x5a;

/// Represents a parsed ASN.1 UTCTime value (X.680 clause 47).
/// UTCTime consists of a calendar date (YYMMDD), time to a precision of minutes or seconds,
/// and an optional local time differential from UTC.
#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]
pub struct UtcTime {
    pub datetime: DateTime,
    pub precision: TimePrecision,
}

impl DeepView for UtcTime {
    type V = UtcTime;

    closed spec fn deep_view(&self) -> Self::V {
        *self
    }
}

pub(crate) proof fn lemma_utc_time_deep_view(value: &UtcTime)
    ensures
        value.deep_view() == *value,
{
}

impl UtcTime {
    /// Validates semantic well-formedness of the UTCTime value.
    /// Under X.680 clause 47.3, year is limited to the range 1950 to 2049.
    pub open spec fn wf(&self) -> bool {
        &&& datetime_wf(self.datetime)
        &&& 1950 <= self.datetime.year <= 2049
        &&& (self.precision == TimePrecision::Minute || self.precision == TimePrecision::Second)
        &&& (self.precision == TimePrecision::Second || self.datetime.second == 0)
    }
}

/// Helper spec function to validate the date and time digit fields of a UTCTime string (YYMMDDhhmm[ss]).
pub open spec fn utc_time_fields_wf(bytes: Seq<u8>, has_seconds: bool) -> bool {
    let second_end = if has_seconds {
        12
    } else {
        10
    };
    &&& digits(bytes, 0, second_end)
    &&& datetime_wf(
        DateTime {
            year: utc_year(decimal2(bytes, 0)),
            month: decimal2(bytes, 2),
            day: decimal2(bytes, 4),
            hour: decimal2(bytes, 6),
            minute: decimal2(bytes, 8),
            second: if has_seconds {
                decimal2(bytes, 10)
            } else {
                0
            },
        },
    )
}

/// Verified executable implementation of `utc_time_fields_wf`.
pub fn utc_time_fields_valid(bytes: &[u8], has_seconds: bool) -> bool
    requires
        if has_seconds {
            12 <= bytes.len()
        } else {
            10 <= bytes.len()
        },
    returns
        utc_time_fields_wf(bytes@, has_seconds),
{
    let end = if has_seconds {
        12
    } else {
        10
    };
    if !is_digits(bytes, 0, end) {
        return false;
    }
    let value = DateTime {
        year: utc_year(decimal_2(bytes, 0)),
        month: decimal_2(bytes, 2),
        day: decimal_2(bytes, 4),
        hour: decimal_2(bytes, 6),
        minute: decimal_2(bytes, 8),
        second: if has_seconds {
            decimal_2(bytes, 10)
        } else {
            0
        },
    };
    datetime_wf(value)
}

/// Spec function validating a UTCTime timezone offset (+hhmm or -hhmm).
pub open spec fn utc_offset_wf(bytes: Seq<u8>, pos: usize) -> bool {
    &&& pos + 5 == bytes.len()
    &&& (bytes[pos as int] == ASCII_PLUS || bytes[pos as int] == ASCII_MINUS)
    &&& digits(bytes, pos as int + 1, pos as int + 5)
    &&& decimal2(bytes, (pos as int + 1) as usize) <= 23
    &&& decimal2(bytes, (pos as int + 3) as usize) <= 59
}

/// Verified executable implementation of `utc_offset_wf`.
pub fn utc_offset_valid(bytes: &[u8], pos: usize) -> bool
    requires
        pos + 5 == bytes.len(),
    returns
        utc_offset_wf(bytes@, pos),
{
    if bytes[pos] != ASCII_PLUS && bytes[pos] != ASCII_MINUS {
        return false;
    }
    if !is_digits(bytes, pos + 1, pos + 5) {
        return false;
    }
    decimal_2(bytes, pos + 1) <= 23 && decimal_2(bytes, pos + 3) <= 59
}

/// Spec function validating the lexical syntax of UTCTime bytes.
/// Under DER (X.690 11.8.1), the timezone offset MUST be Zulu ('Z').
/// Offsets like "+hhmm" or "-hhmm" are only permitted under BER/CER.
pub open spec fn utc_time_lexical_wf<const DER: bool>(bytes: Seq<u8>) -> bool {
    if DER {
        bytes.len() == 13 && bytes[12] == ASCII_Z && utc_time_fields_wf(bytes, true)
    } else {
        ||| bytes.len() == 11 && bytes[10] == ASCII_Z && utc_time_fields_wf(bytes, false)
        ||| bytes.len() == 13 && bytes[12] == ASCII_Z && utc_time_fields_wf(bytes, true)
        ||| bytes.len() == 15 && utc_time_fields_wf(bytes, false) && utc_offset_wf(bytes, 10)
        ||| bytes.len() == 17 && utc_time_fields_wf(bytes, true) && utc_offset_wf(bytes, 12)
    }
}

/// Verified executable implementation of `utc_time_lexical_wf`.
pub fn utc_time_bytes_valid<const DER: bool>(bytes: &[u8]) -> bool
    returns
        utc_time_lexical_wf::<DER>(bytes@),
{
    if DER {
        bytes.len() == 13 && bytes[12] == ASCII_Z && utc_time_fields_valid(bytes, true)
    } else if bytes.len() == 11 {
        bytes[10] == ASCII_Z && utc_time_fields_valid(bytes, false)
    } else if bytes.len() == 13 {
        bytes[12] == ASCII_Z && utc_time_fields_valid(bytes, true)
    } else if bytes.len() == 15 {
        utc_time_fields_valid(bytes, false) && utc_offset_valid(bytes, 10)
    } else if bytes.len() == 17 {
        utc_time_fields_valid(bytes, true) && utc_offset_valid(bytes, 12)
    } else {
        false
    }
}

/// Spec function parsing the UTCTime bytes into a structured `UtcTime`.
/// Properly normalizes the timezone offset (UTC = local - offset) if present.
pub open spec fn utc_time_value(bytes: Seq<u8>) -> Option<UtcTime> {
    let has_seconds = bytes.len() == 13 || bytes.len() == 17;
    let local = DateTime {
        year: utc_year(decimal2(bytes, 0)),
        month: decimal2(bytes, 2),
        day: decimal2(bytes, 4),
        hour: decimal2(bytes, 6),
        minute: decimal2(bytes, 8),
        second: if has_seconds {
            decimal2(bytes, 10)
        } else {
            0
        },
    };
    let precision = if has_seconds {
        TimePrecision::Second
    } else {
        TimePrecision::Minute
    };
    if bytes.len() == 11 || bytes.len() == 13 {
        Some(UtcTime { datetime: local, precision })
    } else {
        let pos: usize = if has_seconds {
            12
        } else {
            10
        };
        match normalize_offset(
            local,
            bytes[pos as int] == ASCII_PLUS,
            decimal2(bytes, (pos as int + 1) as usize),
            decimal2(bytes, (pos as int + 3) as usize),
        ) {
            Some(datetime) => Some(UtcTime { datetime, precision }),
            None => None,
        }
    }
}

/// Verified executable implementation of `utc_time_value`.
pub fn utctime_value(bytes: &[u8]) -> Option<UtcTime>
    requires
        utc_time_lexical_wf::<false>(bytes@),
    returns
        utc_time_value(bytes@),
{
    let has_seconds = bytes.len() == 13 || bytes.len() == 17;
    let local = DateTime {
        year: utc_year(decimal_2(bytes, 0)),
        month: decimal_2(bytes, 2),
        day: decimal_2(bytes, 4),
        hour: decimal_2(bytes, 6),
        minute: decimal_2(bytes, 8),
        second: if has_seconds {
            decimal_2(bytes, 10)
        } else {
            0
        },
    };
    let precision = if has_seconds {
        TimePrecision::Second
    } else {
        TimePrecision::Minute
    };
    if bytes.len() == 11 || bytes.len() == 13 {
        Some(UtcTime { datetime: local, precision })
    } else {
        let pos = if has_seconds {
            12
        } else {
            10
        };
        match normalize_offset(
            local,
            bytes[pos] == ASCII_PLUS,
            decimal_2(bytes, pos + 1),
            decimal_2(bytes, pos + 3),
        ) {
            Some(datetime) => Some(UtcTime { datetime, precision }),
            None => None,
        }
    }
}

/// Spec function validating semantic well-formedness of parsed UTCTime bytes.
/// Under DER (X.690 11.8.2), the seconds element MUST always be present.
pub open spec fn utc_time_bytes_wf<const DER: bool>(bytes: Seq<u8>) -> bool {
    &&& utc_time_lexical_wf::<DER>(bytes)
    &&& utc_time_value(bytes) matches Some(value) ==> value.wf()
    &&& utc_time_value(bytes).is_some()
}

/// Verified executable implementation of `utc_time_bytes_wf`.
pub fn utc_time_valid<const DER: bool>(bytes: &[u8]) -> bool
    returns
        utc_time_bytes_wf::<DER>(bytes@),
{
    if !utc_time_bytes_valid::<DER>(bytes) {
        return false;
    }
    let value = utctime_value(bytes);
    match value {
        Some(value) => {
            datetime_wf(value.datetime) && 1950 <= value.datetime.year && value.datetime.year
                <= 2049 && (value.precision == TimePrecision::Minute || value.precision
                == TimePrecision::Second) && (value.precision == TimePrecision::Second
                || value.datetime.second == 0)
        },
        None => false,
    }
}

/// Spec function mapping `UtcTime` to serialized UTCTime bytes (YYMMDDhhmmssZ or YYMMDDhhmmZ).
#[verusfmt::skip]
pub open spec fn utc_time_bytes(value: UtcTime) -> Seq<u8> {
    let year = (value.datetime.year as int % 100) as u8;
      decimal2_bytes(year)@
    + decimal2_bytes(value.datetime.month)@
    + decimal2_bytes(value.datetime.day)@
    + decimal2_bytes(value.datetime.hour)@
    + decimal2_bytes(value.datetime.minute)@
    + if value.precision == TimePrecision::Second {
        decimal2_bytes(value.datetime.second)@ + seq![ASCII_Z]
    } else {
        seq![ASCII_Z]
    }
}

/// Writes `utc_time_bytes` directly to an output buffer without allocating.
pub fn utc_time_to_bytes<Output: OutputBuf>(value: &UtcTime, obuf: &mut Output)
    requires
        value.wf(),
        old(obuf).fits(utc_time_bytes(*value).len()),
    ensures
        final(obuf)@ == old(obuf)@ + utc_time_bytes(*value),
        forall|n| old(obuf).fits(utc_time_bytes(*value).len() + n) <==> final(obuf).fits(n),
        old(obuf).same_destination(final(obuf)),
{
    broadcast use crate::core::exec::output::outbuf_lemmas;

    let short_year = (value.datetime.year % 100) as u8;
    let year = decimal2_bytes(short_year);
    let month = decimal2_bytes(value.datetime.month);
    let day = decimal2_bytes(value.datetime.day);
    let hour = decimal2_bytes(value.datetime.hour);
    let minute = decimal2_bytes(value.datetime.minute);
    obuf.write_bytes(&year);
    obuf.write_bytes(&month);
    obuf.write_bytes(&day);
    obuf.write_bytes(&hour);
    obuf.write_bytes(&minute);
    if value.precision == TimePrecision::Second {
        let second = decimal2_bytes(value.datetime.second);
        obuf.write_bytes(&second);
    }
    obuf.write_byte(ASCII_Z);
}

// The reverse direction of `lemma_utc_year_short`, also pure arithmetic.
proof fn lemma_utc_year_roundtrip(year: u16)
    requires
        1950 <= year <= 2049,
    ensures
        (year as int % 100) as u8 <= 99,
        utc_year((year as int % 100) as u8) == year,
{
}

// All the decoding facts about `utc_time_bytes`, established once so that the well-formedness
// and round-trip queries never have to redo the sequence-concatenation reasoning.
proof fn lemma_utc_time_bytes_layout(value: UtcTime)
    requires
        value.wf(),
    ensures
        ({
            let bytes = utc_time_bytes(value);
            let end = if value.precision == TimePrecision::Second {
                12int
            } else {
                10int
            };
            &&& bytes.len() == end + 1
            &&& bytes[end] == ASCII_Z
            &&& digits(bytes, 0, end)
            &&& utc_year(decimal2(bytes, 0)) == value.datetime.year
            &&& decimal2(bytes, 2) == value.datetime.month
            &&& decimal2(bytes, 4) == value.datetime.day
            &&& decimal2(bytes, 6) == value.datetime.hour
            &&& decimal2(bytes, 8) == value.datetime.minute
            &&& value.precision == TimePrecision::Second ==> decimal2(bytes, 10)
                == value.datetime.second
        }),
{
    let short_year = (value.datetime.year as int % 100) as u8;
    lemma_utc_year_roundtrip(value.datetime.year);
    lemma_decimal2_roundtrip(short_year);
    lemma_decimal2_roundtrip(value.datetime.month);
    lemma_decimal2_roundtrip(value.datetime.day);
    lemma_decimal2_roundtrip(value.datetime.hour);
    lemma_decimal2_roundtrip(value.datetime.minute);
    lemma_decimal2_roundtrip(value.datetime.second);
}

pub proof fn lemma_utc_time_encode_wf<const DER: bool>(value: UtcTime)
    requires
        value.wf(),
        DER ==> value.precision == TimePrecision::Second,
    ensures
        utc_time_bytes_wf::<DER>(utc_time_bytes(value)),
        utc_time_value(utc_time_bytes(value)) == Some(value),
{
    lemma_utc_time_bytes_layout(value);
}

#[verifier::rlimit(100)]
pub proof fn lemma_der_utc_time_canonical(bytes: Seq<u8>)
    requires
        utc_time_bytes_wf::<true>(bytes),
    ensures
        utc_time_bytes(utc_time_value(bytes)->0) == bytes,
{
    assert(digits(bytes, 0, 12));
    assert(ascii_digit(bytes[0]));
    assert(ascii_digit(bytes[1]));
    lemma_decimal2_canonical(bytes, 0);
    lemma_decimal2_canonical(bytes, 2);
    lemma_decimal2_canonical(bytes, 4);
    lemma_decimal2_canonical(bytes, 6);
    lemma_decimal2_canonical(bytes, 8);
    lemma_decimal2_canonical(bytes, 10);
}

type UtcTimeInnerFmt<const DER: bool> = Mapped<
    Refined<Tail, PredFnSpec<Seq<u8>>>,
    FnSpecMapper<Seq<u8>, UtcTime>,
>;

pub open spec fn utc_time_fmt<const DER: bool>() -> UtcTimeInnerFmt<DER> {
    Mapped {
        inner: Refined(Tail, |bytes: Seq<u8>| utc_time_bytes_wf::<DER>(bytes)),
        mapper: (|bytes: Seq<u8>| utc_time_value(bytes)->0, |value: UtcTime| utc_time_bytes(value)),
    }
}

proof fn lemma_der_utc_time_fmt_sound_nonmal()
    ensures
        utc_time_fmt::<true>().sound_inv(),
        utc_time_fmt::<true>().nonmal_inv(),
{
    assert forall|bytes: Seq<u8>| #[trigger]
        utc_time_fmt::<true>().inner.consistent(bytes) implies (utc_time_fmt::<true>().mapper.1)(
        (utc_time_fmt::<true>().mapper.0)(bytes),
    ) == bytes by {
        lemma_der_utc_time_canonical(bytes);
    }
}

mod derived_specs {
    use super::*;

    impl<const DER: bool> SpecParser for super::super::UtcTimeFmt<DER> {
        type PVal = UtcTime;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            utc_time_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for super::super::UtcTimeFmt<DER> {
        type Val = UtcTime;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            value.wf() && (DER ==> value.precision == TimePrecision::Second)
        }
    }

    impl<const DER: bool> SpecSerializerDps for super::super::UtcTimeFmt<DER> {
        type SValue = UtcTime;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            utc_time_bytes(value)
        }
    }

    impl<const DER: bool> SpecSerializer for super::super::UtcTimeFmt<DER> {
        type SVal = UtcTime;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            utc_time_bytes(value)
        }
    }

    impl<const DER: bool> SpecByteLen for super::super::UtcTimeFmt<DER> {
        type T = UtcTime;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            utc_time_bytes(value).len()
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const DER: bool> SafeParser for super::super::UtcTimeFmt<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            utc_time_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for super::super::UtcTimeFmt<DER> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        }
    }

    impl<const DER: bool> GoodSerializer for super::super::UtcTimeFmt<DER> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
        }
    }

    impl<const DER: bool> EquivSerializers for super::super::UtcTimeFmt<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
        }
    }

    impl<const DER: bool> SPRoundTripDps for super::super::UtcTimeFmt<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            lemma_utc_time_encode_wf::<DER>(value);
        }
    }

    impl SoundParser for super::super::UtcTimeFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_der_utc_time_fmt_sound_nonmal();
            utc_time_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_der_utc_time_fmt_sound_nonmal();
            utc_time_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl NonMalleable for super::super::UtcTimeFmt<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_der_utc_time_fmt_sound_nonmal();
            utc_time_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

}

impl<'i, const DER: bool> Parser<&'i [u8]> for super::UtcTimeFmt<DER> {
    type PT = UtcTime;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        assert(bytes@ == bytes.deep_view());
        if !utc_time_valid::<DER>(bytes) {
            return Err(ParseError::custom("Invalid UTCTime"));
        }
        match utctime_value(bytes) {
            Some(value) => Ok((n, value)),
            None => Err(ParseError::custom("UTCTime offset out of range")),
        }
    }
}

impl<Output: OutputBuf, const DER: bool> Serializer<Output, UtcTime> for super::UtcTimeFmt<DER> {
    fn serialize_into(&self, value: &UtcTime, obuf: &mut Output) {
        proof {
            assert(value.wf());
            assert(DER ==> value.precision == TimePrecision::Second);
            lemma_utc_time_encode_wf::<DER>(*value);
        }
        utc_time_to_bytes(value, obuf);
    }
}

impl<const DER: bool> Prepare<UtcTime> for super::UtcTimeFmt<DER> {
    fn prepare(&self, value: &UtcTime) -> Result<usize, PreSerializeError> {
        if !datetime_wf(value.datetime) || value.datetime.year < 1950 || value.datetime.year > 2049
            || (value.precision != TimePrecision::Minute && value.precision
            != TimePrecision::Second) || (value.precision == TimePrecision::Minute
            && value.datetime.second != 0) || (DER && value.precision != TimePrecision::Second) {
            return Err(PreSerializeError::custom("Invalid UTCTime value"));
        }
        proof {
            assert(value.wf());
            assert(DER ==> value.precision == TimePrecision::Second);
            lemma_utc_time_encode_wf::<DER>(*value);
        }
        Ok(
            if value.precision == TimePrecision::Second {
                13
            } else {
                11
            },
        )
    }
}

impl<const DER: bool> ByteLen<UtcTime> for super::UtcTimeFmt<DER> {
    fn length(&self, value: &UtcTime) -> usize {
        if value.precision == TimePrecision::Second {
            13
        } else {
            11
        }
    }
}

} // verus!
