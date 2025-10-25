use super::*;
use vstd::prelude::*;

verus! {

#[derive(Debug, View, PolyfillClone)]
pub enum UTCTimeZone {
    UTC,
    UTCPlus(u8, u8),
    UTCMinus(u8, u8),
}

#[derive(Debug, View, PolyfillClone)]
pub struct UTCTimeValueInner {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: OptionDeep<u8>,
    pub time_zone: UTCTimeZone,
}

pub type SpecUTCTimeValue = UTCTimeValueInner;
pub type UTCTimeValue<'a> = UTCTimeValueInner;
pub type UTCTimeValueOwned = UTCTimeValueInner;

/// Parse UTCTime string in 6 formats
/// - YYMMDDhhmmZ
/// - YYMMDDhhmmssZ
/// - YYMMDDhhmm+hhmm
/// - YYMMDDhhmm-hhmm
/// - YYMMDDhhmmss+hhmm
/// - YYMMDDhhmmss-hhmm
#[derive(Debug, View)]
pub struct UTCTime;

asn1_tagged!(UTCTime, tag_of!(UTC_TIME));

impl SpecCombinator for UTCTime {
    type SpecResult = UTCTimeValueInner;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        LengthWrapped(UTCTimeInner).spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        LengthWrapped(UTCTimeInner).spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        LengthWrapped(UTCTimeInner).spec_serialize(v)
    }
}

impl SecureSpecCombinator for UTCTime {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        LengthWrapped(UTCTimeInner).theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        LengthWrapped(UTCTimeInner).theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        LengthWrapped(UTCTimeInner).lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for UTCTime {
    type Result<'a> = UTCTimeValueInner;
    type Owned = UTCTimeValueInner;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn parse<'a>(&self, v: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        LengthWrapped(UTCTimeInner).parse(v)
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        LengthWrapped(UTCTimeInner).serialize(v, data, pos)
    }
}

#[derive(Debug, View)]
pub struct UTCTimeInner;

/// We can't use return or ? in spec, so this helper function
/// helps to simplify the spec code
///
/// Also due to parsing issues in Verus + macro, we need to
/// keep two versions of let_some! for both spec and exec
#[allow(unused_macros)]
macro_rules! spec_let_some {
    ({ $body:expr }) => {
        ::builtin_macros::verus_proof_expr! {
            $body
        }
    };

    ($var:ident = $opt:expr; $($rest_var:ident = $rest_opt:expr;)* { $body:expr }) => {
        ::builtin_macros::verus_proof_expr! {
            if let Some($var) = $opt {
                spec_let_some!($($rest_var = $rest_opt;)* { $body })
            } else {
                Err(())
            }
        }
    };
}
pub(super) use spec_let_some;

#[allow(unused_macros)]
macro_rules! let_some {
    ($_:expr, { $body:expr }) => {
        $body
    };

    ($err:expr, $var:ident = $opt:expr; $($rest_var:ident = $rest_opt:expr;)* { $body:expr }) => {
        if let Some($var) = $opt {
            let_some!($err, $($rest_var = $rest_opt;)* { $body })
        } else {
            Err($err)
        }
    };
}
pub(super) use let_some;

impl SpecCombinator for UTCTimeInner {
    type SpecResult = UTCTimeValueInner;

    closed spec fn spec_parse(&self, v: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        spec_let_some!(
            year = two_chars_to_u8(v[0], v[1]);
            month = two_chars_to_u8(v[2], v[3]);
            day = two_chars_to_u8(v[4], v[5]);
            hour = two_chars_to_u8(v[6], v[7]);
            minute = two_chars_to_u8(v[8], v[9]);

            {{
                let year = if year >= 50 {
                    (1900 + year) as u16
                } else {
                    (2000 + year) as u16
                };

                if v.len() == 11 && v[10] == 'Z' as u8 {
                    // YYMMDDhhmmZ
                    Ok((v.len() as usize, UTCTimeValueInner {
                        year: year,
                        month: month,
                        day: day,
                        hour: hour,
                        minute: minute,
                        second: OptionDeep::None,
                        time_zone: UTCTimeZone::UTC,
                    }))
                } else if v.len() == 13 && v[12] == 'Z' as u8 {
                    // YYMMDDhhmmssZ
                    spec_let_some!(
                        second = two_chars_to_u8(v[10], v[11]);
                        {{
                            Ok((v.len() as usize, UTCTimeValueInner {
                                year: year,
                                month: month,
                                day: day,
                                hour: hour,
                                minute: minute,
                                second: OptionDeep::Some(second),
                                time_zone: UTCTimeZone::UTC,
                            }))
                        }}
                    )
                } else if v.len() == 15 && (v[10] == '+' as u8 || v[10] == '-' as u8) {
                    // YYMMDDhhmm+hhmm
                    // YYMMDDhhmm-hhmm

                    spec_let_some!(
                        offset_hour = two_chars_to_u8(v[11], v[12]);
                        offset_minute = two_chars_to_u8(v[13], v[14]);
                        {{
                            Ok((v.len() as usize, UTCTimeValueInner {
                                year: year,
                                month: month,
                                day: day,
                                hour: hour,
                                minute: minute,
                                second: OptionDeep::None,
                                time_zone: if v[10] == '+' as u8 {
                                    UTCTimeZone::UTCPlus(offset_hour, offset_minute)
                                } else {
                                    UTCTimeZone::UTCMinus(offset_hour, offset_minute)
                                },
                            }))
                        }}
                    )
                } else if v.len() == 17 && (v[12] == '+' as u8 || v[12] == '-' as u8) {
                    // YYMMDDhhmmss+hhmm
                    // YYMMDDhhmmss-hhmm

                    spec_let_some!(
                        second = two_chars_to_u8(v[10], v[11]);
                        offset_hour = two_chars_to_u8(v[13], v[14]);
                        offset_minute = two_chars_to_u8(v[15], v[16]);
                        {{
                            Ok((v.len() as usize, UTCTimeValueInner {
                                year: year,
                                month: month,
                                day: day,
                                hour: hour,
                                minute: minute,
                                second: OptionDeep::Some(second),
                                time_zone: if v[12] == '+' as u8 {
                                    UTCTimeZone::UTCPlus(offset_hour, offset_minute)
                                } else {
                                    UTCTimeZone::UTCMinus(offset_hour, offset_minute)
                                },
                            }))
                        }}
                    )
                } else {
                    Err(())
                }
            }}
        )
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        spec_let_some!(
            year = if 1950 <= v.year && v.year <= 2049 {
                u8_to_two_chars((v.year % 100) as u8)
            } else {
                None
            };
            month = u8_to_two_chars(v.month);
            day = u8_to_two_chars(v.day);
            hour = u8_to_two_chars(v.hour);
            minute = u8_to_two_chars(v.minute);

            {{
                match (v.second, v.time_zone) {
                    // YYMMDDhhmmZ
                    (OptionDeep::None, UTCTimeZone::UTC) =>
                        Ok(seq![
                            year.0, year.1,
                            month.0, month.1,
                            day.0, day.1,
                            hour.0, hour.1,
                            minute.0, minute.1,
                            'Z' as u8,
                        ]),

                    // YYMMDDhhmmssZ
                    (OptionDeep::Some(second), UTCTimeZone::UTC) =>
                        spec_let_some!(
                            second = u8_to_two_chars(second);
                            {{ Ok(seq![
                                year.0, year.1,
                                month.0, month.1,
                                day.0, day.1,
                                hour.0, hour.1,
                                minute.0, minute.1,
                                second.0, second.1,
                                'Z' as u8
                            ])}}
                        ),

                    // YYMMDDhhmm+hhmm
                    // YYMMDDhhmm-hhmm
                    (OptionDeep::None, UTCTimeZone::UTCPlus(off_hour, off_minute)) |
                    (OptionDeep::None, UTCTimeZone::UTCMinus(off_hour, off_minute)) =>
                        spec_let_some!(
                            off_hour = u8_to_two_chars(off_hour);
                            off_minute = u8_to_two_chars(off_minute);
                            {{ Ok(seq![
                                year.0, year.1,
                                month.0, month.1,
                                day.0, day.1,
                                hour.0, hour.1,
                                minute.0, minute.1,
                                if let UTCTimeZone::UTCPlus(..) = v.time_zone { '+' as u8 } else { '-' as u8 },
                                off_hour.0, off_hour.1,
                                off_minute.0, off_minute.1
                            ])}}),

                    // YYMMDDhhmmss+hhmm
                    // YYMMDDhhmmss-hhmm
                    (OptionDeep::Some(second), UTCTimeZone::UTCPlus(off_hour, off_minute)) |
                    (OptionDeep::Some(second), UTCTimeZone::UTCMinus(off_hour, off_minute)) =>
                        spec_let_some!(
                            second = u8_to_two_chars(second);
                            off_hour = u8_to_two_chars(off_hour);
                            off_minute = u8_to_two_chars(off_minute);
                            {{ Ok(seq![
                                year.0, year.1,
                                month.0, month.1,
                                day.0, day.1,
                                hour.0, hour.1,
                                minute.0, minute.1,
                                second.0, second.1,
                                if let UTCTimeZone::UTCPlus(..) = v.time_zone { '+' as u8 } else { '-' as u8 },
                                off_hour.0, off_hour.1,
                                off_minute.0, off_minute.1
                            ])}}
                        ),
                }
            }}
        )
    }
}

impl SecureSpecCombinator for UTCTimeInner {
    open spec fn is_prefix_secure() -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(buf) = self.spec_serialize(v) {
            broadcast use lemma_two_chars_to_u8_iso, lemma_u8_to_two_chars_iso;
            assert(self.spec_parse(buf).unwrap().1 =~= v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((len, v)) = self.spec_parse(buf) {
            broadcast use lemma_two_chars_to_u8_iso, lemma_u8_to_two_chars_iso;
            assert(self.spec_serialize(v).unwrap() =~= buf);
            assert(buf.subrange(0, len as int) =~= buf);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl Combinator for UTCTimeInner {
    type Result<'a> = UTCTimeValueInner;
    type Owned = UTCTimeValueInner;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn parse<'a>(&self, v: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if v.len() < 10 {
            return Err(ParseError::Other("Invalid UTCTime".to_string()));
        }

        let_some!(
            ParseError::Other("Invalid UTCTime".to_string()),
            year = two_chars_to_u8(v[0], v[1]);
            month = two_chars_to_u8(v[2], v[3]);
            day = two_chars_to_u8(v[4], v[5]);
            hour = two_chars_to_u8(v[6], v[7]);
            minute = two_chars_to_u8(v[8], v[9]);

            {{
                let year = if year >= 50 {
                    1900 + year as u16
                } else {
                    2000 + year as u16
                };

                if v.len() == 11 && v[10] == 'Z' as u8 {
                    // YYMMDDhhmmZ
                    Ok((v.len(), UTCTimeValueInner {
                        year: year,
                        month: month,
                        day: day,
                        hour: hour,
                        minute: minute,
                        second: OptionDeep::None,
                        time_zone: UTCTimeZone::UTC,
                    }))
                } else if v.len() == 13 && v[12] == 'Z' as u8 {
                    // YYMMDDhhmmssZ
                    let_some!(
                        ParseError::Other("Invalid UTCTime".to_string()),
                        second = two_chars_to_u8(v[10], v[11]);
                        {{
                            Ok((v.len(), UTCTimeValueInner {
                                year: year,
                                month: month,
                                day: day,
                                hour: hour,
                                minute: minute,
                                second: OptionDeep::Some(second),
                                time_zone: UTCTimeZone::UTC,
                            }))
                        }}
                    )
                } else if v.len() == 15 && (v[10] == '+' as u8 || v[10] == '-' as u8) {
                    // YYMMDDhhmm+hhmm
                    // YYMMDDhhmm-hhmm

                    let_some!(
                        ParseError::Other("Invalid UTCTime".to_string()),
                        offset_hour = two_chars_to_u8(v[11], v[12]);
                        offset_minute = two_chars_to_u8(v[13], v[14]);
                        {{
                            Ok((v.len(), UTCTimeValueInner {
                                year: year,
                                month: month,
                                day: day,
                                hour: hour,
                                minute: minute,
                                second: OptionDeep::None,
                                time_zone: if v[10] == '+' as u8 {
                                    UTCTimeZone::UTCPlus(offset_hour, offset_minute)
                                } else {
                                    UTCTimeZone::UTCMinus(offset_hour, offset_minute)
                                },
                            }))
                        }}
                    )
                } else if v.len() == 17 && (v[12] == '+' as u8 || v[12] == '-' as u8) {
                    // YYMMDDhhmmss+hhmm
                    // YYMMDDhhmmss-hhmm

                    let_some!(
                        ParseError::Other("Invalid UTCTime".to_string()),
                        second = two_chars_to_u8(v[10], v[11]);
                        offset_hour = two_chars_to_u8(v[13], v[14]);
                        offset_minute = two_chars_to_u8(v[15], v[16]);
                        {{
                            Ok((v.len(), UTCTimeValueInner {
                                year: year,
                                month: month,
                                day: day,
                                hour: hour,
                                minute: minute,
                                second: OptionDeep::Some(second),
                                time_zone: if v[12] == '+' as u8 {
                                    UTCTimeZone::UTCPlus(offset_hour, offset_minute)
                                } else {
                                    UTCTimeZone::UTCMinus(offset_hour, offset_minute)
                                },
                            }))
                        }}
                    )
                } else {
                    Err(ParseError::Other("Invalid UTCTime".to_string()))
                }
            }}
        )
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let res = let_some!(
            SerializeError::Other("Invalid UTCTime".to_string()),
            year = if 1950 <= v.year && v.year <= 2049 {
                u8_to_two_chars((v.year % 100) as u8)
            } else {
                None
            };
            month = u8_to_two_chars(v.month);
            day = u8_to_two_chars(v.day);
            hour = u8_to_two_chars(v.hour);
            minute = u8_to_two_chars(v.minute);

            {{
                match (v.second, &v.time_zone) {
                    // YYMMDDhhmmZ
                    (OptionDeep::None, UTCTimeZone::UTC) => {
                        if pos <= usize::MAX - 11 && pos + 11 <= data.len() {
                            data.set(pos, year.0); data.set(pos + 1, year.1);
                            data.set(pos + 2, month.0); data.set(pos + 3, month.1);
                            data.set(pos + 4, day.0); data.set(pos + 5, day.1);
                            data.set(pos + 6, hour.0); data.set(pos + 7, hour.1);
                            data.set(pos + 8, minute.0); data.set(pos + 9, minute.1);
                            data.set(pos + 10, 'Z' as u8);
                            Ok(11)
                        } else {
                            Err(SerializeError::InsufficientBuffer)
                        }
                    }

                    // YYMMDDhhmmssZ
                    (OptionDeep::Some(second), UTCTimeZone::UTC) =>
                        let_some!(
                            SerializeError::Other("Invalid UTCTime".to_string()),
                            second = u8_to_two_chars(second);
                            {{
                                if pos <= usize::MAX - 13 && pos + 13 <= data.len() {
                                    data.set(pos, year.0); data.set(pos + 1, year.1);
                                    data.set(pos + 2, month.0); data.set(pos + 3, month.1);
                                    data.set(pos + 4, day.0); data.set(pos + 5, day.1);
                                    data.set(pos + 6, hour.0); data.set(pos + 7, hour.1);
                                    data.set(pos + 8, minute.0); data.set(pos + 9, minute.1);
                                    data.set(pos + 10, second.0); data.set(pos + 11, second.1);
                                    data.set(pos + 12, 'Z' as u8);
                                    Ok(13)
                                } else {
                                    Err(SerializeError::InsufficientBuffer)
                                }
                            }}
                        ),

                    // YYMMDDhhmm+hhmm
                    // YYMMDDhhmm-hhmm
                    (OptionDeep::None, UTCTimeZone::UTCPlus(off_hour, off_minute)) |
                    (OptionDeep::None, UTCTimeZone::UTCMinus(off_hour, off_minute)) =>
                        let_some!(
                            SerializeError::Other("Invalid UTCTime".to_string()),
                            off_hour = u8_to_two_chars(*off_hour);
                            off_minute = u8_to_two_chars(*off_minute);
                            {{
                                if pos <= usize::MAX - 15 && pos + 15 <= data.len() {
                                    data.set(pos, year.0); data.set(pos + 1, year.1);
                                    data.set(pos + 2, month.0); data.set(pos + 3, month.1);
                                    data.set(pos + 4, day.0); data.set(pos + 5, day.1);
                                    data.set(pos + 6, hour.0); data.set(pos + 7, hour.1);
                                    data.set(pos + 8, minute.0); data.set(pos + 9, minute.1);
                                    data.set(pos + 10, if let UTCTimeZone::UTCPlus(..) = v.time_zone { '+' as u8 } else { '-' as u8 });
                                    data.set(pos + 11, off_hour.0); data.set(pos + 12, off_hour.1);
                                    data.set(pos + 13, off_minute.0); data.set(pos + 14, off_minute.1);
                                    Ok(15)
                                } else {
                                    Err(SerializeError::InsufficientBuffer)
                                }
                            }}),

                    // YYMMDDhhmmss+hhmm
                    // YYMMDDhhmmss-hhmm
                    (OptionDeep::Some(second), UTCTimeZone::UTCPlus(off_hour, off_minute)) |
                    (OptionDeep::Some(second), UTCTimeZone::UTCMinus(off_hour, off_minute)) =>
                        let_some!(
                            SerializeError::Other("Invalid UTCTime".to_string()),
                            second = u8_to_two_chars(second);
                            off_hour = u8_to_two_chars(*off_hour);
                            off_minute = u8_to_two_chars(*off_minute);
                            {{
                                if pos <= usize::MAX - 17 && pos + 17 <= data.len() {
                                    data.set(pos, year.0); data.set(pos + 1, year.1);
                                    data.set(pos + 2, month.0); data.set(pos + 3, month.1);
                                    data.set(pos + 4, day.0); data.set(pos + 5, day.1);
                                    data.set(pos + 6, hour.0); data.set(pos + 7, hour.1);
                                    data.set(pos + 8, minute.0); data.set(pos + 9, minute.1);
                                    data.set(pos + 10, second.0); data.set(pos + 11, second.1);
                                    data.set(pos + 12, if let UTCTimeZone::UTCPlus(..) = v.time_zone { '+' as u8 } else { '-' as u8 });
                                    data.set(pos + 13, off_hour.0); data.set(pos + 14, off_hour.1);
                                    data.set(pos + 15, off_minute.0); data.set(pos + 16, off_minute.1);
                                    Ok(17)
                                } else {
                                    Err(SerializeError::InsufficientBuffer)
                                }
                            }}
                        ),
                }
            }}
        );

        if res.is_ok() {
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
        }

        res
    }
}

macro_rules! zero_char { {} => { '0' as u8 }; }
macro_rules! nine_char { {} => { '9' as u8 }; }

/// Conversion between u8 (< 100) and two ASCII chars
#[verifier::opaque]
pub closed spec fn spec_two_chars_to_u8(b1: u8, b2: u8) -> Option<u8> {
    if b1 >= zero_char!() && b1 <= nine_char!() && b2 >= zero_char!() && b2 <= nine_char!() {
        Some(((b1 - zero_char!()) * 10 + (b2 - zero_char!())) as u8)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn spec_u8_to_two_chars(v: u8) -> Option<(u8, u8)> {
    if v >= 100 {
        None
    } else {
        let b1 = v / 10;
        let b2 = v % 10;

        Some(((b1 + zero_char!()) as u8, (b2 + zero_char!()) as u8))
    }
}

pub broadcast proof fn lemma_two_chars_to_u8_iso(b1: u8, b2: u8)
    ensures
        #[trigger] spec_two_chars_to_u8(b1, b2) matches Some(v) ==> {
            &&& 0 <= v < 100
            &&& spec_u8_to_two_chars(v) matches Some(r)
            &&& r == (b1, b2)
        }
{
    reveal(spec_two_chars_to_u8);
    reveal(spec_u8_to_two_chars);
}

pub broadcast proof fn lemma_u8_to_two_chars_iso(v: u8)
    ensures
        #[trigger] spec_u8_to_two_chars(v) matches Some((b1, b2)) ==> {
            &&& spec_two_chars_to_u8(b1, b2) matches Some(a)
            &&& a == v
        },
        spec_u8_to_two_chars(v).is_none() <==> v >= 100
{
    reveal(spec_two_chars_to_u8);
    reveal(spec_u8_to_two_chars);
}

#[verifier::when_used_as_spec(spec_two_chars_to_u8)]
pub fn two_chars_to_u8(b1: u8, b2: u8) -> (res: Option<u8>)
    ensures
        res matches Some(res) ==> {
            &&& spec_two_chars_to_u8(b1, b2) matches Some(res2)
            &&& res == res2
        },
        res.is_none() ==> spec_two_chars_to_u8(b1, b2).is_none()
{
    reveal(spec_two_chars_to_u8);
    if b1 >= zero_char!() && b1 <= nine_char!() && b2 >= zero_char!() && b2 <= nine_char!() {
        Some(((b1 - zero_char!()) * 10 + (b2 - zero_char!())) as u8)
    } else {
        None
    }
}

#[verifier::when_used_as_spec(spec_u8_to_two_chars)]
pub fn u8_to_two_chars(v: u8) -> (res: Option<(u8, u8)>)
    ensures
        res matches Some(res) ==> {
            &&& spec_u8_to_two_chars(v) matches Some(res2)
            &&& res2 == res
        },
        res.is_none() ==> spec_u8_to_two_chars(v).is_none(),
{
    reveal(spec_u8_to_two_chars);
    if v >= 100 {
        None
    } else {
        let b1 = v / 10;
        let b2 = v % 10;

        Some(((b1 + zero_char!()) as u8, (b2 + zero_char!()) as u8))
    }
}

}
