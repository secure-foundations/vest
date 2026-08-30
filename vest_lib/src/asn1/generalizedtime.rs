//! ASN.1 GeneralizedTime values and contents format.
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::{
    combinators::{
        mapped::spec::{LosslessMapper, LossyMapper, SpecMapper},
        Mapped, Refined, Tail,
    },
    core::{proof::*, spec::*},
};
use vstd::assert_seqs_equal;
use vstd::prelude::*;
use OutputBuf;

use super::datetime::*;

verus! {

/// Logical specification of an ASN.1 GeneralizedTime value (X.680 clause 46).
/// Consists of a calendar date (YYYYMMDD), local time of day, optional fractional
/// seconds, and a timezone offset or Zulu UTC indicator.
#[verifier::ext_equal]
pub struct GeneralizedTimeSpec {
    pub datetime: DateTime,
    pub precision: TimePrecision,
    pub fraction: Seq<u8>,
    pub zone: TimeZone,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GeneralizedTime<'a> {
    pub datetime: DateTime,
    pub precision: TimePrecision,
    pub fraction: &'a [u8],
    pub zone: TimeZone,
}

impl<'a> DeepView for GeneralizedTime<'a> {
    type V = GeneralizedTimeSpec;

    closed spec fn deep_view(&self) -> Self::V {
        GeneralizedTimeSpec {
            datetime: self.datetime,
            precision: self.precision,
            fraction: self.fraction@,
            zone: self.zone,
        }
    }
}

impl GeneralizedTimeSpec {
    /// Validates semantic well-formedness of the GeneralizedTime value.
    /// Year must be represented using 4 digits (up to 9999).
    pub open spec fn wf(&self) -> bool {
        &&& datetime_wf(self.datetime)
        &&& self.datetime.year <= 9999
        &&& digits(self.fraction, 0, self.fraction.len() as int)
        &&& (self.precision == TimePrecision::Hour || self.precision == TimePrecision::Minute
            || self.precision == TimePrecision::Second)
        &&& (self.precision != TimePrecision::Hour || (self.datetime.minute == 0
            && self.datetime.second == 0))
        &&& (self.precision != TimePrecision::Minute || self.datetime.second == 0)
    }

    /// Validates DER-specific restrictions for GeneralizedTime (X.690 clause 11.7):
    /// - The encoding MUST terminate with 'Z' (meaning UTC only).
    /// - The seconds element MUST always be present.
    /// - Fractional seconds, if present, MUST omit all trailing zeros (and cannot end in '0').
    pub open spec fn der_wf(&self) -> bool {
        &&& self.wf()
        &&& self.zone == TimeZone::Utc
        &&& self.precision == TimePrecision::Second
        &&& (self.fraction.len() == 0 || self.fraction.last() != 0x30)
    }
}

impl<'a> GeneralizedTime<'a> {
    pub fn new(
        datetime: DateTime,
        precision: TimePrecision,
        fraction: &'a [u8],
        zone: TimeZone,
    ) -> (value: Self)
        requires
            (GeneralizedTimeSpec { datetime, precision, fraction: fraction@, zone }).wf(),
        ensures
            value.deep_view() == (GeneralizedTimeSpec {
                datetime,
                precision,
                fraction: fraction@,
                zone,
            }),
    {
        GeneralizedTime { datetime, precision, fraction, zone }
    }

    pub fn fraction(&self) -> (fraction: &'a [u8])
        ensures
            fraction.deep_view() == self.deep_view().fraction,
    {
        self.fraction
    }
}

/// Helper spec function to validate the prefix date-time fields (YYYYMMDDhh[mm[ss]]).
pub open spec fn generalized_fields_wf(bytes: Seq<u8>, main_end: usize) -> bool {
    &&& (main_end == 10 || main_end == 12 || main_end == 14)
    &&& digits(bytes, 0, main_end as int)
    &&& datetime_wf(
        DateTime {
            year: decimal4(bytes, 0),
            month: decimal2(bytes, 4),
            day: decimal2(bytes, 6),
            hour: decimal2(bytes, 8),
            minute: if main_end >= 12 {
                decimal2(bytes, 10)
            } else {
                0
            },
            second: if main_end == 14 {
                decimal2(bytes, 12)
            } else {
                0
            },
        },
    )
}

/// Verified executable implementation of `generalized_fields_wf`.
pub fn generalized_fields_valid(bytes: &[u8], main_end: usize) -> bool
    requires
        main_end <= bytes.len(),
    returns
        generalized_fields_wf(bytes@, main_end),
{
    if main_end != 10 && main_end != 12 && main_end != 14 {
        return false;
    }
    if !is_digits(bytes, 0, main_end) {
        return false;
    }
    let value = DateTime {
        year: decimal_4(bytes, 0),
        month: decimal_2(bytes, 4),
        day: decimal_2(bytes, 6),
        hour: decimal_2(bytes, 8),
        minute: if main_end >= 12 {
            decimal_2(bytes, 10)
        } else {
            0
        },
        second: if main_end == 14 {
            decimal_2(bytes, 12)
        } else {
            0
        },
    };
    datetime_wf(value)
}

/// Spec function validating the optional fractional-seconds element of GeneralizedTime.
/// Under BER (X.680 46.3.a.2), either a comma (0x2c) or a full stop (0x2e) is allowed as the decimal separator.
/// Under DER (X.690 11.7.3-11.7.4):
/// - The decimal separator MUST be a full stop (0x2e / '.').
/// - Trailing zeros are forbidden in the fractional part (i.e. cannot end with ASCII '0').
pub open spec fn generalized_fraction_wf<const DER: bool>(
    bytes: Seq<u8>,
    main_end: usize,
    zone_start: usize,
) -> bool {
    if zone_start == main_end {
        true
    } else {
        &&& main_end + 1 < zone_start
        &&& (bytes[main_end as int] == 0x2e || (!DER && bytes[main_end as int] == 0x2c))
        &&& digits(bytes, main_end as int + 1, zone_start as int)
        &&& (!DER || bytes[zone_start as int - 1] != 0x30)
    }
}

/// Verified executable implementation of `generalized_fraction_wf`.
pub fn generalized_fraction_valid<const DER: bool>(
    bytes: &[u8],
    main_end: usize,
    zone_start: usize,
) -> bool
    requires
        main_end <= zone_start <= bytes.len(),
    returns
        generalized_fraction_wf::<DER>(bytes@, main_end, zone_start),
{
    if zone_start == main_end {
        return true;
    }
    if main_end + 1 >= zone_start {
        return false;
    }
    if bytes[main_end] != 0x2e && (DER || bytes[main_end] != 0x2c) {
        return false;
    }
    is_digits(bytes, main_end + 1, zone_start) && (!DER || bytes[zone_start - 1] != 0x30)
}

/// Spec function validating the timezone suffix (Zulu or UTC offset).
/// Under DER (X.690 11.7.1), only Zulu ('Z') is allowed.
/// Under BER, UTC offsets like `+hhmm`, `-hhmm`, `+hh`, or `-hh` (omitting minutes component) are allowed.
pub open spec fn generalized_zone_wf<const DER: bool>(bytes: Seq<u8>, zone_start: usize) -> bool {
    if DER {
        zone_start + 1 == bytes.len() && bytes[zone_start as int] == 0x5a
    } else {
        ||| zone_start == bytes.len()
        ||| zone_start + 1 == bytes.len() && bytes[zone_start as int] == 0x5a
        ||| zone_start + 3 == bytes.len() && (bytes[zone_start as int] == 0x2b
            || bytes[zone_start as int] == 0x2d) && digits(
            bytes,
            zone_start as int + 1,
            zone_start as int + 3,
        ) && decimal2(bytes, (zone_start as int + 1) as usize) <= 23
        ||| zone_start + 5 == bytes.len() && (bytes[zone_start as int] == 0x2b
            || bytes[zone_start as int] == 0x2d) && digits(
            bytes,
            zone_start as int + 1,
            zone_start as int + 5,
        ) && decimal2(bytes, (zone_start as int + 1) as usize) <= 23 && decimal2(
            bytes,
            (zone_start as int + 3) as usize,
        ) <= 59
    }
}

/// Verified executable implementation of `generalized_zone_wf`.
pub fn generalized_zone_valid<const DER: bool>(bytes: &[u8], zone_start: usize) -> bool
    requires
        zone_start <= bytes.len(),
    returns
        generalized_zone_wf::<DER>(bytes@, zone_start),
{
    if DER {
        return bytes.len() - zone_start == 1 && bytes[zone_start] == 0x5a;
    }
    if zone_start == bytes.len() {
        return true;
    }
    if bytes.len() - zone_start == 1 {
        return bytes[zone_start] == 0x5a;
    }
    if bytes[zone_start] != 0x2b && bytes[zone_start] != 0x2d {
        return false;
    }
    if bytes.len() - zone_start == 3 {
        return is_digits(bytes, zone_start + 1, zone_start + 3) && decimal_2(bytes, zone_start + 1)
            <= 23;
    }
    bytes.len() - zone_start == 5 && is_digits(bytes, zone_start + 1, zone_start + 5) && decimal_2(
        bytes,
        zone_start + 1,
    ) <= 23 && decimal_2(bytes, zone_start + 3) <= 59
}

pub open spec fn generalized_candidate_wf<const DER: bool>(
    bytes: Seq<u8>,
    main_end: usize,
    zone_start: usize,
) -> bool {
    &&& main_end <= zone_start <= bytes.len()
    &&& generalized_fields_wf(bytes, main_end)
    &&& generalized_fraction_wf::<DER>(bytes, main_end, zone_start)
    &&& generalized_zone_wf::<DER>(bytes, zone_start)
}

/// Verified executable implementation of `generalized_candidate_wf`.
pub fn generalized_candidate_valid<const DER: bool>(
    bytes: &[u8],
    main_end: usize,
    zone_start: usize,
) -> bool
    requires
        zone_start <= bytes.len(),
    returns
        generalized_candidate_wf::<DER>(bytes@, main_end, zone_start),
{
    main_end <= zone_start && generalized_fields_valid(bytes, main_end)
        && generalized_fraction_valid::<DER>(bytes, main_end, zone_start)
        && generalized_zone_valid::<DER>(bytes, zone_start)
}

/// Spec function validating the overall structure of GeneralizedTime bytes.
/// Under DER, it forces `main_end = 14` (seconds component must always be present).
/// Under BER, it permits `main_end` to be 10 (hours), 12 (minutes), or 14 (seconds).
pub open spec fn generalized_time_bytes_wf<const DER: bool>(bytes: Seq<u8>) -> bool {
    let zone_start = generalized_zone_start(bytes);
    if DER {
        generalized_candidate_wf::<true>(bytes, 14, zone_start)
    } else {
        ||| generalized_candidate_wf::<false>(bytes, 10, zone_start)
        ||| generalized_candidate_wf::<false>(bytes, 12, zone_start)
        ||| generalized_candidate_wf::<false>(bytes, 14, zone_start)
    }
}

/// Verified executable implementation of `generalized_time_bytes_wf`.
pub fn generalized_time_bytes_valid<const DER: bool>(bytes: &[u8]) -> bool
    returns
        generalized_time_bytes_wf::<DER>(bytes@),
{
    let zone_start = generalized_zonestart(bytes);
    if DER {
        generalized_candidate_valid::<true>(bytes, 14, zone_start)
    } else {
        generalized_candidate_valid::<false>(bytes, 10, zone_start)
            || generalized_candidate_valid::<false>(bytes, 12, zone_start)
            || generalized_candidate_valid::<false>(bytes, 14, zone_start)
    }
}

/// Spec function identifying the start index of the timezone suffix in GeneralizedTime bytes.
/// The timezone suffix can be 'Z' (Zulu), '+hhmm', '-hhmm', '+hh', '-hh', or omitted (local time).
pub open spec fn generalized_zone_start(bytes: Seq<u8>) -> usize {
    let len = bytes.len();
    if len > 0 && bytes[len - 1] == 0x5a {
        (len - 1) as usize
    } else if len >= 3 && (bytes[len - 3] == 0x2b || bytes[len - 3] == 0x2d) {
        (len - 3) as usize
    } else if len >= 5 && (bytes[len - 5] == 0x2b || bytes[len - 5] == 0x2d) {
        (len - 5) as usize
    } else {
        len as usize
    }
}

/// Verified executable implementation of `generalized_zone_start`.
pub fn generalized_zonestart(bytes: &[u8]) -> (zone_start: usize)
    ensures
        zone_start <= bytes.len(),
    returns
        generalized_zone_start(bytes@),
{
    let len = bytes.len();
    if len > 0 && bytes[len - 1] == 0x5a {
        len - 1
    } else if len >= 3 && (bytes[len - 3] == 0x2b || bytes[len - 3] == 0x2d) {
        len - 3
    } else if len >= 5 && (bytes[len - 5] == 0x2b || bytes[len - 5] == 0x2d) {
        len - 5
    } else {
        len
    }
}

/// Spec function identifying the end index of the main date-time prefix (YYYYMMDDhh[mm[ss]]).
pub open spec fn generalized_main_end(bytes: Seq<u8>, zone_start: usize) -> usize {
    if generalized_candidate_wf::<false>(bytes, 10, zone_start) {
        10
    } else if generalized_candidate_wf::<false>(bytes, 12, zone_start) {
        12
    } else {
        14
    }
}

/// Verified executable implementation of `generalized_main_end`.
pub fn generalized_mainend(bytes: &[u8], zone_start: usize) -> usize
    requires
        generalized_time_bytes_wf::<false>(bytes@),
        zone_start == generalized_zone_start(bytes@),
    returns
        generalized_main_end(bytes@, zone_start),
{
    if generalized_candidate_valid::<false>(bytes, 10, zone_start) {
        10
    } else if generalized_candidate_valid::<false>(bytes, 12, zone_start) {
        12
    } else {
        14
    }
}

/// Spec function parsing the parsed GeneralizedTime bytes into a structured `GeneralizedTimeSpec`.
/// Handles timezone offset adjustment (UTC = local - offset) if present.
pub open spec fn generalized_time_value(bytes: Seq<u8>) -> Option<GeneralizedTimeSpec> {
    let zone_start = generalized_zone_start(bytes);
    let main_end = generalized_main_end(bytes, zone_start);
    let local = DateTime {
        year: decimal4(bytes, 0),
        month: decimal2(bytes, 4),
        day: decimal2(bytes, 6),
        hour: decimal2(bytes, 8),
        minute: if main_end >= 12 {
            decimal2(bytes, 10)
        } else {
            0
        },
        second: if main_end == 14 {
            decimal2(bytes, 12)
        } else {
            0
        },
    };
    let precision = if main_end == 10 {
        TimePrecision::Hour
    } else if main_end == 12 {
        TimePrecision::Minute
    } else {
        TimePrecision::Second
    };
    let fraction = if main_end == zone_start {
        Seq::empty()
    } else {
        bytes.subrange(main_end as int + 1, zone_start as int)
    };
    if zone_start == bytes.len() || bytes[zone_start as int] == 0x5a {
        Some(
            GeneralizedTimeSpec {
                datetime: local,
                precision,
                fraction,
                zone: if zone_start == bytes.len() {
                    TimeZone::Local
                } else {
                    TimeZone::Utc
                },
            },
        )
    } else {
        let offset_minute = if bytes.len() - zone_start == 5 {
            decimal2(bytes, (zone_start as int + 3) as usize)
        } else {
            0
        };
        match normalize_offset(
            local,
            bytes[zone_start as int] == 0x2b,
            decimal2(bytes, (zone_start as int + 1) as usize),
            offset_minute,
        ) {
            Some(datetime) => Some(
                GeneralizedTimeSpec { datetime, precision, fraction, zone: TimeZone::Utc },
            ),
            None => None,
        }
    }
}

/// Verified executable implementation of `generalized_time_value`.
/// Decodes the byte sequence into a `GeneralizedTime`.
#[verifier::rlimit(20)]
pub fn generalized_timevalue<'a>(bytes: &'a [u8]) -> (res: Option<GeneralizedTime<'a>>)
    requires
        generalized_time_bytes_wf::<false>(bytes@),
    ensures
        res.deep_view() == generalized_time_value(bytes@),
{
    let zone_start = generalized_zonestart(bytes);
    let main_end = generalized_mainend(bytes, zone_start);
    let local = DateTime {
        year: decimal_4(bytes, 0),
        month: decimal_2(bytes, 4),
        day: decimal_2(bytes, 6),
        hour: decimal_2(bytes, 8),
        minute: if main_end >= 12 {
            decimal_2(bytes, 10)
        } else {
            0
        },
        second: if main_end == 14 {
            decimal_2(bytes, 12)
        } else {
            0
        },
    };
    let precision = if main_end == 10 {
        TimePrecision::Hour
    } else if main_end == 12 {
        TimePrecision::Minute
    } else {
        TimePrecision::Second
    };
    let fraction = if main_end == zone_start {
        &bytes[main_end..main_end]
    } else {
        &bytes[main_end + 1..zone_start]
    };
    if zone_start == bytes.len() || bytes[zone_start] == 0x5a {
        Some(
            GeneralizedTime {
                datetime: local,
                precision,
                fraction,
                zone: if zone_start == bytes.len() {
                    TimeZone::Local
                } else {
                    TimeZone::Utc
                },
            },
        )
    } else {
        let offset_minute = if bytes.len() - zone_start == 5 {
            decimal_2(bytes, zone_start + 3)
        } else {
            0
        };
        match normalize_offset(
            local,
            bytes[zone_start] == 0x2b,
            decimal_2(bytes, zone_start + 1),
            offset_minute,
        ) {
            Some(datetime) => Some(
                GeneralizedTime { datetime, precision, fraction, zone: TimeZone::Utc },
            ),
            None => None,
        }
    }
}

/// Spec function validating full well-formedness of GeneralizedTime bytes.
pub open spec fn generalized_time_wf<const DER: bool>(bytes: Seq<u8>) -> bool {
    &&& generalized_time_bytes_wf::<DER>(bytes)
    &&& generalized_time_value(bytes) matches Some(value) ==> value.wf()
    &&& generalized_time_value(bytes).is_some()
    &&& bytes.len() <= usize::MAX
}

/// Verified executable implementation of `generalized_time_wf`.
pub fn generalized_time_valid<const DER: bool>(bytes: &[u8]) -> bool
    returns
        generalized_time_wf::<DER>(bytes@),
{
    assert(bytes@.len() == bytes.len());
    assert(bytes@.len() <= usize::MAX);
    if !generalized_time_bytes_valid::<DER>(bytes) {
        return false;
    }
    match generalized_timevalue(bytes) {
        Some(value) => generalized_value_wf::<false>(&value),
        None => false,
    }
}

pub open spec fn generalized_time_prefix(value: GeneralizedTimeSpec) -> Seq<u8> {
    decimal4_bytes(value.datetime.year)@ + decimal2_bytes(value.datetime.month)@ + decimal2_bytes(
        value.datetime.day,
    )@ + decimal2_bytes(value.datetime.hour)@ + if value.precision == TimePrecision::Hour {
        Seq::empty()
    } else {
        decimal2_bytes(value.datetime.minute)@ + if value.precision == TimePrecision::Second {
            decimal2_bytes(value.datetime.second)@
        } else {
            Seq::empty()
        }
    }
}

pub open spec fn generalized_time_fraction(value: GeneralizedTimeSpec) -> Seq<u8> {
    if value.fraction.len() == 0 {
        Seq::empty()
    } else {
        seq![0x2eu8] + value.fraction
    }
}

pub open spec fn generalized_time_suffix(value: GeneralizedTimeSpec) -> Seq<u8> {
    if value.zone == TimeZone::Utc {
        seq![0x5au8]
    } else {
        Seq::empty()
    }
}

pub open spec fn generalized_time_bytes(value: GeneralizedTimeSpec) -> Seq<u8> {
    generalized_time_prefix(value) + generalized_time_fraction(value) + generalized_time_suffix(
        value,
    )
}

pub(crate) fn generalized_time_der_prefix_bytes<'a>(value: &GeneralizedTime<'a>) -> (bytes:
    [u8; 14])
    requires
        value.deep_view().der_wf(),
    ensures
        bytes@ == generalized_time_prefix(value.deep_view()),
{
    let year = decimal4_bytes(value.datetime.year);
    let month = decimal2_bytes(value.datetime.month);
    let day = decimal2_bytes(value.datetime.day);
    let hour = decimal2_bytes(value.datetime.hour);
    let minute = decimal2_bytes(value.datetime.minute);
    let second = decimal2_bytes(value.datetime.second);
    [
        year[0],
        year[1],
        year[2],
        year[3],
        month[0],
        month[1],
        day[0],
        day[1],
        hour[0],
        hour[1],
        minute[0],
        minute[1],
        second[0],
        second[1],
    ]
}

/// Writes a `GeneralizedTime` directly to an output buffer without allocating.
pub fn generalized_time_to_bytes<'a, Output: OutputBuf>(
    value: &GeneralizedTime<'a>,
    obuf: &mut Output,
)
    requires
        value.deep_view().wf(),
        old(obuf).fits(generalized_time_bytes(value.deep_view()).len()),
    ensures
        final(obuf)@ == old(obuf)@ + generalized_time_bytes(value.deep_view()),
        forall|n|
            old(obuf).fits(generalized_time_bytes(value.deep_view()).len() + n)
                <==> final(obuf).fits(n),
        old(obuf).same_destination(final(obuf)),
{
    broadcast use crate::core::exec::output::outbuf_lemmas;

    let year = decimal4_bytes(value.datetime.year);
    let month = decimal2_bytes(value.datetime.month);
    let day = decimal2_bytes(value.datetime.day);
    let hour = decimal2_bytes(value.datetime.hour);
    obuf.write_bytes(&year);
    obuf.write_bytes(&month);
    obuf.write_bytes(&day);
    obuf.write_bytes(&hour);
    if value.precision != TimePrecision::Hour {
        let minute = decimal2_bytes(value.datetime.minute);
        obuf.write_bytes(&minute);
        if value.precision == TimePrecision::Second {
            let second = decimal2_bytes(value.datetime.second);
            obuf.write_bytes(&second);
        }
    }
    if value.fraction.len() > 0 {
        obuf.write_byte(0x2e);
        obuf.write_bytes(value.fraction);
    }
    if value.zone == TimeZone::Utc {
        obuf.write_byte(0x5a);
    }
}

/// Executable view validation helper checking well-formedness of `GeneralizedTime`.
#[verifier::allow_in_spec]
pub fn generalized_value_wf<'a, const DER: bool>(value: &GeneralizedTime<'a>) -> bool
    returns
        if DER {
            value.deep_view().der_wf()
        } else {
            value.deep_view().wf()
        },
{
    let base = datetime_wf(value.datetime) && value.datetime.year <= 9999 && is_digits(
        value.fraction,
        0,
        value.fraction.len(),
    ) && (value.precision == TimePrecision::Hour || value.precision == TimePrecision::Minute
        || value.precision == TimePrecision::Second) && (value.precision != TimePrecision::Hour || (
    value.datetime.minute == 0 && value.datetime.second == 0)) && (value.precision
        != TimePrecision::Minute || value.datetime.second == 0);
    base && (!DER || (value.zone == TimeZone::Utc && value.precision == TimePrecision::Second && (
    value.fraction.len() == 0 || value.fraction[value.fraction.len() - 1] != 0x30)))
}

pub open spec fn generalized_time_len(value: GeneralizedTimeSpec) -> nat {
    10 as nat + if value.precision == TimePrecision::Hour {
        0 as nat
    } else {
        2 as nat
    } + if value.precision == TimePrecision::Second {
        2 as nat
    } else {
        0 as nat
    } + if value.fraction.len() == 0 {
        0 as nat
    } else {
        1 + value.fraction.len()
    } + if value.zone == TimeZone::Utc {
        1 as nat
    } else {
        0 as nat
    }
}

spec fn generalized_time_main_end(value: GeneralizedTimeSpec) -> usize {
    if value.precision == TimePrecision::Hour {
        10
    } else if value.precision == TimePrecision::Minute {
        12
    } else {
        14
    }
}

spec fn generalized_time_zone_start(value: GeneralizedTimeSpec) -> usize {
    (generalized_time_main_end(value) + generalized_time_fraction(value).len()) as usize
}

// Keep sequence-heavy reasoning in separate solver queries and export only decoded facts.
#[verifier::rlimit(20)]
proof fn lemma_generalized_time_encoded_prefix(value: GeneralizedTimeSpec)
    requires
        value.wf(),
        generalized_time_len(value) <= usize::MAX,
    ensures
        generalized_time_prefix(value).len() == generalized_time_main_end(value),
        generalized_fields_wf(generalized_time_bytes(value), generalized_time_main_end(value)),
        decimal4(generalized_time_bytes(value), 0) == value.datetime.year,
        decimal2(generalized_time_bytes(value), 4) == value.datetime.month,
        decimal2(generalized_time_bytes(value), 6) == value.datetime.day,
        decimal2(generalized_time_bytes(value), 8) == value.datetime.hour,
        value.precision != TimePrecision::Hour ==> decimal2(generalized_time_bytes(value), 10)
            == value.datetime.minute,
        value.precision == TimePrecision::Second ==> decimal2(generalized_time_bytes(value), 12)
            == value.datetime.second,
{
    lemma_decimal4_roundtrip(value.datetime.year);
    lemma_decimal2_roundtrip(value.datetime.month);
    lemma_decimal2_roundtrip(value.datetime.day);
    lemma_decimal2_roundtrip(value.datetime.hour);
    lemma_decimal2_roundtrip(value.datetime.minute);
    lemma_decimal2_roundtrip(value.datetime.second);
}

#[verifier::rlimit(20)]
proof fn lemma_generalized_time_encoded_fraction<const DER: bool>(value: GeneralizedTimeSpec)
    requires
        if DER {
            value.der_wf()
        } else {
            value.wf()
        },
        generalized_time_len(value) <= usize::MAX,
    ensures
        generalized_fraction_wf::<DER>(
            generalized_time_bytes(value),
            generalized_time_main_end(value),
            generalized_time_zone_start(value),
        ),
        if generalized_time_main_end(value) == generalized_time_zone_start(value) {
            value.fraction.len() == 0
        } else {
            generalized_time_bytes(value).subrange(
                generalized_time_main_end(value) as int + 1,
                generalized_time_zone_start(value) as int,
            ) == value.fraction
        },
{
    let prefix = generalized_time_prefix(value);
    let fraction = generalized_time_fraction(value);
    let suffix = generalized_time_suffix(value);
    let bytes = prefix + fraction + suffix;
    let main_end = generalized_time_main_end(value);
    let zone_start: usize = (main_end + fraction.len()) as usize;

    if value.fraction.len() == 0 {
    } else {
        assert(fraction == seq![0x2eu8] + value.fraction);
        assert_seqs_equal!(bytes.subrange(main_end as int + 1, zone_start as int) == value.fraction, i => {
            assert(bytes[main_end as int + 1 + i] == fraction[1 + i]);
            assert(fraction[1 + i] == value.fraction[i]);
        });
        assert(digits(bytes, main_end as int + 1, zone_start as int)) by {
            assert forall|i: int| main_end <= i < zone_start - 1 implies ascii_digit(
                #[trigger] bytes[i + 1],
            ) by {
                assert(bytes[i + 1] == value.fraction[i - main_end]);
            }
        }
        assert(generalized_fraction_wf::<DER>(bytes, main_end, zone_start));
    }
}

#[verifier::rlimit(20)]
proof fn lemma_generalized_time_encoded_zone<const DER: bool>(value: GeneralizedTimeSpec)
    requires
        if DER {
            value.der_wf()
        } else {
            value.wf()
        },
        generalized_time_len(value) <= usize::MAX,
    ensures
        generalized_zone_start(generalized_time_bytes(value)) == generalized_time_zone_start(value),
        generalized_zone_wf::<DER>(
            generalized_time_bytes(value),
            generalized_time_zone_start(value),
        ),
        (generalized_time_zone_start(value) == generalized_time_bytes(value).len()) <==> value.zone
            == TimeZone::Local,
        value.zone == TimeZone::Utc ==> generalized_time_bytes(value)[generalized_time_zone_start(
            value,
        ) as int] == 0x5a,
{
}

#[verifier::rlimit(20)]
proof fn lemma_generalized_time_encoded_layout<const DER: bool>(value: GeneralizedTimeSpec)
    requires
        if DER {
            value.der_wf()
        } else {
            value.wf()
        },
        generalized_time_len(value) <= usize::MAX,
    ensures
        generalized_time_bytes_wf::<DER>(generalized_time_bytes(value)),
        generalized_main_end(generalized_time_bytes(value), generalized_time_zone_start(value))
            == generalized_time_main_end(value),
{
    lemma_generalized_time_encoded_prefix(value);
    lemma_generalized_time_encoded_fraction::<DER>(value);
    lemma_generalized_time_encoded_zone::<DER>(value);
}

#[verifier::rlimit(20)]
pub proof fn lemma_generalized_time_encode_roundtrip<const DER: bool>(value: GeneralizedTimeSpec)
    requires
        if DER {
            value.der_wf()
        } else {
            value.wf()
        },
        generalized_time_len(value) <= usize::MAX,
    ensures
        generalized_time_wf::<DER>(generalized_time_bytes(value)),
        generalized_time_value(generalized_time_bytes(value)) == Some(value),
        generalized_time_bytes(value).len() == generalized_time_len(value),
{
    lemma_generalized_time_encoded_layout::<DER>(value);
    lemma_generalized_time_encoded_prefix(value);
    lemma_generalized_time_encoded_fraction::<DER>(value);
    lemma_generalized_time_encoded_zone::<DER>(value);
}

#[verifier::rlimit(100)]
pub proof fn lemma_der_generalized_time_canonical(bytes: Seq<u8>)
    requires
        generalized_time_wf::<true>(bytes),
    ensures
        generalized_time_bytes(generalized_time_value(bytes).unwrap()) == bytes,
{
    lemma_decimal4_canonical(bytes, 0);
    lemma_decimal2_canonical(bytes, 4);
    lemma_decimal2_canonical(bytes, 6);
    lemma_decimal2_canonical(bytes, 8);
    lemma_decimal2_canonical(bytes, 10);
    lemma_decimal2_canonical(bytes, 12);
}

mod derived_specs {
    use super::*;

    impl<const DER: bool> SpecParser for super::super::GeneralizedTimeFmt<DER> {
        type PVal = GeneralizedTimeSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            if generalized_time_wf::<DER>(ibuf) {
                Some((ibuf.len() as int, generalized_time_value(ibuf).unwrap()))
            } else {
                None
            }
        }
    }

    impl<const DER: bool> Consistency for super::super::GeneralizedTimeFmt<DER> {
        type Val = GeneralizedTimeSpec;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            (if DER {
                value.der_wf()
            } else {
                value.wf()
            }) && generalized_time_len(value) <= usize::MAX
        }
    }

    impl<const DER: bool> SpecSerializerDps for super::super::GeneralizedTimeFmt<DER> {
        type SValue = GeneralizedTimeSpec;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            generalized_time_bytes(value)
        }
    }

    impl<const DER: bool> SpecSerializer for super::super::GeneralizedTimeFmt<DER> {
        type SVal = GeneralizedTimeSpec;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            generalized_time_bytes(value)
        }
    }

    impl<const DER: bool> SpecByteLen for super::super::GeneralizedTimeFmt<DER> {
        type T = GeneralizedTimeSpec;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            generalized_time_len(value)
        }
    }

}

pub(crate) proof fn lemma_der_generalized_time_model(value: GeneralizedTimeSpec)
    requires
        super::GeneralizedTimeFmt::<true>.consistent(value),
    ensures
        value.der_wf(),
        super::GeneralizedTimeFmt::<true>.spec_serialize(value) == generalized_time_prefix(value)
            + generalized_time_fraction(value) + generalized_time_suffix(value),
        super::GeneralizedTimeFmt::<true>.spec_serialize(value).len()
            == super::GeneralizedTimeFmt::<true>.byte_len(value),
        super::GeneralizedTimeFmt::<true>.spec_serialize(value).len() <= usize::MAX,
        generalized_time_prefix(value).len() == 14,
        generalized_time_suffix(value) == seq![0x5au8],
{
}

pub(crate) proof fn lemma_der_generalized_time_layout(value: GeneralizedTimeSpec, pos: usize)
    requires
        super::GeneralizedTimeFmt::<true>.consistent(value),
    ensures
        super::GeneralizedTimeFmt::<true>.spec_serialize(value).len() == if value.fraction.len()
            == 0 {
            15
        } else {
            value.fraction.len() + 16
        },
        pos < super::GeneralizedTimeFmt::<true>.spec_serialize(value).len() ==> {
            super::GeneralizedTimeFmt::<true>.spec_serialize(value)[pos as int] == if pos < 14 {
                generalized_time_prefix(value)[pos as int]
            } else if value.fraction.len() == 0 {
                0x5au8
            } else if pos == 14 {
                0x2eu8
            } else if (pos as nat) < value.fraction.len() + 15 {
                value.fraction[pos as int - 15]
            } else {
                0x5au8
            }
        },
{
    lemma_der_generalized_time_model(value);
}

mod derived_proofs {
    use super::*;

    impl<const DER: bool> SafeParser for super::super::GeneralizedTimeFmt<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        }
    }

    impl<const DER: bool> Productive for super::super::GeneralizedTimeFmt<DER> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            if let Some((n, _)) = self.spec_parse(ibuf) {
                assert(n == ibuf.len());
                assert(n >= 10);
            }
        }
    }

    impl<const DER: bool> GoodSerializer for super::super::GeneralizedTimeFmt<DER> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
        }
    }

    impl<const DER: bool> EquivSerializers for super::super::GeneralizedTimeFmt<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
        }
    }

    impl<const DER: bool> SPRoundTripDps for super::super::GeneralizedTimeFmt<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            lemma_generalized_time_encode_roundtrip::<DER>(value);
        }
    }

    impl SoundParser for super::super::GeneralizedTimeFmt<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            if let Some((n, value)) = self.spec_parse(ibuf) {
                lemma_der_generalized_time_canonical(ibuf);
                assert(generalized_time_bytes(value) == ibuf);
            }
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            if let Some((_, value)) = self.spec_parse(ibuf) {
                lemma_der_generalized_time_canonical(ibuf);
                assert(value.der_wf());
                assert(generalized_time_len(value) <= usize::MAX);
            }
        }
    }

    impl NonMalleable for super::super::GeneralizedTimeFmt<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            if let (Some((n1, value1)), Some((n2, value2))) = (
                self.spec_parse(buf1),
                self.spec_parse(buf2),
            ) {
                lemma_der_generalized_time_canonical(buf1);
                lemma_der_generalized_time_canonical(buf2);
                if value1 == value2 {
                    assert(buf1 == generalized_time_bytes(value1));
                    assert(buf2 == generalized_time_bytes(value2));
                    assert(buf1.take(n1) == buf1);
                    assert(buf2.take(n2) == buf2);
                }
            }
        }
    }

}

impl<'i, const DER: bool> Parser<&'i [u8]> for super::GeneralizedTimeFmt<DER> {
    type PT = GeneralizedTime<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        assert(bytes@ == bytes.deep_view());
        if !generalized_time_valid::<DER>(bytes) {
            return Err(ParseError::custom("Invalid GeneralizedTime"));
        }
        match generalized_timevalue(bytes) {
            Some(value) => Ok((n, value)),
            None => Err(ParseError::custom("GeneralizedTime offset out of range")),
        }
    }
}

impl<Output: OutputBuf, 'i, const DER: bool> Serializer<
    Output,
    GeneralizedTime<'i>,
> for super::GeneralizedTimeFmt<DER> {
    fn serialize_into(&self, value: &GeneralizedTime<'i>, obuf: &mut Output) {
        generalized_time_to_bytes(value, obuf);
    }
}

impl<'i, const DER: bool> Prepare<GeneralizedTime<'i>> for super::GeneralizedTimeFmt<DER> {
    fn prepare(&self, value: &GeneralizedTime<'i>) -> Result<usize, PreSerializeError> {
        if !generalized_value_wf::<DER>(value) {
            return Err(PreSerializeError::custom("Invalid GeneralizedTime value"));
        }
        if value.fraction.len() > usize::MAX - 16 {
            return Err(PreSerializeError::length_too_large());
        }
        Ok(
            10 + if value.precision == TimePrecision::Hour {
                0
            } else {
                2
            } + if value.precision == TimePrecision::Second {
                2
            } else {
                0
            } + if value.fraction.len() == 0 {
                0
            } else {
                1 + value.fraction.len()
            } + if value.zone == TimeZone::Utc {
                1
            } else {
                0
            },
        )
    }
}

impl<'i, const DER: bool> ByteLen<GeneralizedTime<'i>> for super::GeneralizedTimeFmt<DER> {
    fn length(&self, value: &GeneralizedTime<'i>) -> usize {
        10 + if value.precision == TimePrecision::Hour {
            0
        } else {
            2
        } + if value.precision == TimePrecision::Second {
            2
        } else {
            0
        } + if value.fraction.len() == 0 {
            0
        } else {
            1 + value.fraction.len()
        } + if value.zone == TimeZone::Utc {
            1
        } else {
            0
        }
    }
}

} // verus!
