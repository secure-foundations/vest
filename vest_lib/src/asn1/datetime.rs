//! Shared logical date, time, precision, and time-zone representations.
use vstd::arithmetic::div_mod::*;
use vstd::calc;
use vstd::prelude::*;

macro_rules! is_ly {
    ($year:expr) => {
        $year % 4 == 0 && ($year % 100 != 0 || $year % 400 == 0)
    };
}

macro_rules! dim {
    ($year:expr, $month:expr) => {
        if $month == 2 {
            if is_ly!($year) {
                29u8
            } else {
                28u8
            }
        } else if $month == 4 || $month == 6 || $month == 9 || $month == 11 {
            30u8
        } else if $month >= 1 && $month <= 12 {
            31u8
        } else {
            0u8
        }
    };
}

macro_rules! utc_yr {
    ($short_year:expr) => {
        if $short_year >= 50u8 {
            (1900u16 + $short_year as u16) as u16
        } else {
            (2000u16 + $short_year as u16) as u16
        }
    };
}

macro_rules! dt_wf {
    ($value:expr) => {
        1 <= $value.month
            && $value.month <= 12
            && 1 <= $value.day
            && $value.day <= days_in_month($value.year, $value.month)
            && $value.hour <= 23
            && $value.minute <= 59
            && $value.second <= 59
    };
}

macro_rules! nxt_dy {
    ($value:expr) => {
        if $value.day < days_in_month($value.year, $value.month) {
            Some(DateTime {
                day: ($value.day + 1) as u8,
                ..$value
            })
        } else if $value.month < 12 {
            Some(DateTime {
                month: ($value.month + 1) as u8,
                day: 1,
                ..$value
            })
        } else if $value.year < u16::MAX {
            Some(DateTime {
                year: ($value.year + 1) as u16,
                month: 1,
                day: 1,
                ..$value
            })
        } else {
            None
        }
    };
}

macro_rules! prev_dy {
    ($value:expr) => {
        if $value.day > 1 {
            Some(DateTime {
                day: ($value.day - 1) as u8,
                ..$value
            })
        } else if $value.month > 1 {
            Some(DateTime {
                month: ($value.month - 1) as u8,
                day: days_in_month($value.year, ($value.month - 1) as u8),
                ..$value
            })
        } else if $value.year > 0 {
            Some(DateTime {
                year: ($value.year - 1) as u16,
                month: 12,
                day: 31,
                ..$value
            })
        } else {
            None
        }
    };
}

verus! {

/// ASCII code for '0'
pub const ASCII_0: u8 = 0x30;

/// ASCII code for '9'
pub const ASCII_9: u8 = 0x39;

/// A standard date and time representation (year, month, day, hour, minute, second).
#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]
pub struct DateTime {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

impl DeepView for DateTime {
    type V = DateTime;

    closed spec fn deep_view(&self) -> Self::V {
        *self
    }
}

/// Precision indicator for ASN.1 GeneralizedTime and UTCTime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]
pub enum TimePrecision {
    /// Accurate to the hour
    Hour,
    /// Accurate to the minute
    Minute,
    /// Accurate to the second
    Second,
}

/// Time zone indicator (Local or UTC/Zulu).
#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]
pub enum TimeZone {
    /// Local time without an offset, or local time with a timezone offset
    Local,
    /// Coordinated Universal Time (indicated by 'Z' suffix)
    Utc,
}

/// Checks if the given year is a leap year according to the Gregorian calendar.
#[verifier::allow_in_spec]
pub fn is_leap_year(year: u16) -> bool
    returns
        is_ly!(year),
{
    is_ly!(year)
}

/// Returns the number of days in the specified month of a given year.
/// Handles February leap years (29 days). Invalid months return 0.
#[verifier::allow_in_spec]
pub fn days_in_month(year: u16, month: u8) -> u8
    returns
        dim!(year, month),
{
    dim!(year, month)
}

/// Interprets the two-digit UTCTime year (YY) as a four-digit year (YYYY).
/// As per ASN.1 UTCTime specification (X.680 47.3):
/// - Years >= 50 are interpreted as 1950-1999
/// - Years < 50 are interpreted as 2000-2049
#[verifier::allow_in_spec]
pub fn utc_year(short_year: u8) -> u16
    returns
        utc_yr!(short_year),
{
    utc_yr!(short_year)
}

pub open spec fn decimal2(bytes: Seq<u8>, pos: usize) -> u8 {
    ((bytes[pos as int] - ASCII_0) * 10 + (bytes[pos as int + 1] - ASCII_0)) as u8
}

pub fn decimal_2(bytes: &[u8], pos: usize) -> u8
    requires
        pos < usize::MAX,
        pos + 1 < bytes.len(),
        ascii_digit(bytes@[pos as int]),
        ascii_digit(bytes@[pos as int + 1]),
    returns
        decimal2(bytes@, pos),
{
    ((bytes[pos] - ASCII_0) * 10 + (bytes[pos + 1] - ASCII_0)) as u8
}

#[verusfmt::skip]
pub open spec fn decimal4(bytes: Seq<u8>, pos: usize) -> u16
{
    ((
        (bytes[pos as int] - ASCII_0) as u16 * 1000u16)
        + ((bytes[pos + 1] - ASCII_0) as u16 * 100u16)
        + ((bytes[pos + 2] - ASCII_0) as u16 * 10u16)
        +  (bytes[pos + 3] - ASCII_0) as u16) as u16
}

pub fn decimal_4(bytes: &[u8], pos: usize) -> u16
    requires
        pos <= usize::MAX - 3,
        pos + 3 < bytes.len(),
        ascii_digit(bytes@[pos as int]),
        ascii_digit(bytes@[pos as int + 1]),
        ascii_digit(bytes@[pos as int + 2]),
        ascii_digit(bytes@[pos as int + 3]),
    returns
        decimal4(bytes@, pos),
{
    (((bytes[pos] - ASCII_0) as u16 * 1000u16) + ((bytes[pos + 1] - ASCII_0) as u16 * 100u16) + ((
    bytes[pos + 2] - ASCII_0) as u16 * 10u16) + (bytes[pos + 3] - ASCII_0) as u16) as u16
}

#[verifier::allow_in_spec]
pub fn datetime_wf(value: DateTime) -> bool
    returns
        dt_wf!(value),
{
    dt_wf!(value)
}

pub open spec fn ascii_digit(byte: u8) -> bool {
    ASCII_0 <= byte <= ASCII_9
}

#[verifier::allow_in_spec]
pub fn decimal2_bytes(value: u8) -> [u8; 2]
    requires
        value <= 99,
    returns
        [(ASCII_0 + value / 10) as u8, (ASCII_0 + value % 10) as u8],
{
    [ASCII_0 + value / 10, ASCII_0 + value % 10]
}

#[verifier::allow_in_spec]
pub fn decimal4_bytes(value: u16) -> [u8; 4]
    requires
        value <= 9999,
    returns
        [
            (ASCII_0 + value as int / 1000) as u8,
            (ASCII_0 + value as int / 100 % 10) as u8,
            (ASCII_0 + value as int / 10 % 10) as u8,
            (ASCII_0 + value as int % 10) as u8,
        ],
{
    [
        ASCII_0 + (value / 1000) as u8,
        ASCII_0 + ((value / 100) % 10) as u8,
        ASCII_0 + ((value / 10) % 10) as u8,
        ASCII_0 + (value % 10) as u8,
    ]
}

pub broadcast proof fn lemma_decimal2_roundtrip(value: u8)
    requires
        value <= 99,
    ensures
        digits(#[trigger] decimal2_bytes(value)@, 0, 2),
        decimal2(decimal2_bytes(value)@, 0) == value,
{
}

pub broadcast proof fn lemma_decimal2_canonical(bytes: Seq<u8>, pos: usize)
    requires
        pos + 2 <= bytes.len(),
        digits(bytes, pos as int, pos as int + 2),
    ensures
        #[trigger] decimal2_bytes(decimal2(bytes, pos))@ == bytes.subrange(
            pos as int,
            pos as int + 2,
        ),
{
}

#[verifier::rlimit(50)]
pub broadcast proof fn lemma_decimal4_roundtrip(value: u16)
    requires
        value <= 9999,
    ensures
        digits(#[trigger] decimal4_bytes(value)@, 0, 4),
        decimal4(decimal4_bytes(value)@, 0) == value,
{
    // Arithmetic normalization is discharged once here for all time formats.
}

#[verifier::rlimit(20)]
pub proof fn lemma_decimal4_canonical(bytes: Seq<u8>, pos: usize)
    requires
        pos <= usize::MAX - 2,
        pos + 4 <= bytes.len(),
        digits(bytes, pos as int, pos as int + 4),
    ensures
        decimal4_bytes(decimal4(bytes, pos))@ == bytes.subrange(pos as int, pos as int + 4),
{
    lemma_decimal2_canonical(bytes, pos);
    lemma_decimal2_canonical(bytes, (pos as int + 2) as usize);
}

pub open spec fn digits(bytes: Seq<u8>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= bytes.len()
    &&& forall|i: int| start <= i < end ==> ascii_digit(#[trigger] bytes[i])
}

pub fn is_digits(bytes: &[u8], start: usize, end: usize) -> bool
    requires
        start <= end <= bytes.len(),
    returns
        digits(bytes@, start as int, end as int),
{
    for i in start..end
        invariant
            start <= i <= end <= bytes.len(),
            forall|j: int| start <= j < i ==> ascii_digit(#[trigger] bytes@[j]),
    {
        if bytes[i] < ASCII_0 || bytes[i] > ASCII_9 {
            return false;
        }
    }
    true
}

#[verifier::allow_in_spec]
pub fn next_day(value: DateTime) -> (res: Option<DateTime>)
    requires
        datetime_wf(value),
    ensures
        res matches Some(next) ==> datetime_wf(next),
    returns
        nxt_dy!(value),
{
    nxt_dy!(value)
}

#[verifier::allow_in_spec]
pub fn previous_day(value: DateTime) -> (res: Option<DateTime>)
    requires
        datetime_wf(value),
    ensures
        res matches Some(previous) ==> datetime_wf(previous),
    returns
        prev_dy!(value),
{
    prev_dy!(value)
}

/// Adjusts the local time to UTC by subtracting the timezone offset (UTC = local - offset).
/// As per ASN.1 UTCTime (X.680 47.3) and GeneralizedTime (X.680 46.3) specifications:
/// - The timezone offset represents the difference between local time and UTC.
/// - If `local_ahead_of_utc` is true (indicated by '+'), the local time is ahead of UTC,
///   so the offset is subtracted: `UTC = local - offset`.
/// - If `local_ahead_of_utc` is false (indicated by '-'), the local time is behind UTC,
///   so the offset is added: `UTC = local + offset`.
/// - Properly rolls over the calendar date to the next or previous day if necessary.
#[verifier::allow_in_spec]
pub fn normalize_offset(
    local: DateTime,
    local_ahead_of_utc: bool,
    offset_hour: u8,
    offset_minute: u8,
) -> (res: Option<DateTime>)
    requires
        datetime_wf(local),
        offset_hour <= 23,
        offset_minute <= 59,
    ensures
        res matches Some(utc) ==> datetime_wf(utc),
    returns
        ({
            let local_minutes = local.hour as i32 * 60 + local.minute as i32;
            let offset = offset_hour as i32 * 60 + offset_minute as i32;
            let utc_minutes = if local_ahead_of_utc {
                local_minutes - offset
            } else {
                local_minutes + offset
            };
            if utc_minutes < 0 {
                previous_day(
                    DateTime {
                        hour: ((utc_minutes + 1440) / 60) as u8,
                        minute: ((utc_minutes + 1440) % 60) as u8,
                        ..local
                    },
                )
            } else if utc_minutes >= 1440 {
                next_day(
                    DateTime {
                        hour: ((utc_minutes - 1440) / 60) as u8,
                        minute: ((utc_minutes - 1440) % 60) as u8,
                        ..local
                    },
                )
            } else {
                Some(
                    DateTime {
                        hour: (utc_minutes / 60) as u8,
                        minute: (utc_minutes % 60) as u8,
                        ..local
                    },
                )
            }
        }),
{
    let local_minutes = local.hour as i32 * 60 + local.minute as i32;
    let offset = offset_hour as i32 * 60 + offset_minute as i32;
    let utc_minutes = if local_ahead_of_utc {
        local_minutes - offset
    } else {
        local_minutes + offset
    };
    if utc_minutes < 0 {
        previous_day(
            DateTime {
                hour: ((utc_minutes + 1440) / 60) as u8,
                minute: ((utc_minutes + 1440) % 60) as u8,
                ..local
            },
        )
    } else if utc_minutes >= 1440 {
        next_day(
            DateTime {
                hour: ((utc_minutes - 1440) / 60) as u8,
                minute: ((utc_minutes - 1440) % 60) as u8,
                ..local
            },
        )
    } else {
        Some(DateTime { hour: (utc_minutes / 60) as u8, minute: (utc_minutes % 60) as u8, ..local })
    }
}

} // verus!
