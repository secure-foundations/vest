use super::*;
use vstd::prelude::*;

verus! {

#[derive(Debug, View, PolyfillClone)]
pub enum GeneralizedTimeZone {
    UTC,
    Local,
    UTCPlus(u8, u8),
    UTCMinus(u8, u8),
}

#[derive(Debug, View, PolyfillClone)]
pub struct GeneralizedTimeValueInner {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: OptionDeep<u8>,
    pub second: OptionDeep<u8>,
    pub fraction: OptionDeep<u16>,
    pub time_zone: GeneralizedTimeZone,
}

pub type SpecGeneralizedTimeValue = GeneralizedTimeValueInner;
pub type GeneralizedTimeValue<'a> = GeneralizedTimeValueInner;
pub type GeneralizedTimeValueOwned = GeneralizedTimeValueInner;

macro_rules! zero_char { {} => { '0' as u8 }; }
macro_rules! nine_char { {} => { '9' as u8 }; }

/// TODO: this file is a bit of mess, clean it up
///
/// Three formats, each with 4 variants (<https://obj-sys.com/asn1tutorial/node14.html>):
/// 1. Local time only. `YYYYMMDDHH[MM[SS[.fff]]]`, where the optional fff is accurate to three decimal places.
///    Possible lengths: 10, 12, 14, 18.
///
/// 2. Universal time (UTC time) only. `YYYYMMDDHH[MM[SS[.fff]]]Z`.
///    Possible lengths: 11, 13, 15, 19.
///
/// 3. Difference between local and UTC times. `YYYYMMDDHH[MM[SS[.fff]]]+-HHMM`.
///    Possible lengths: 15, 17, 19, 23.
#[derive(Debug, View)]
pub struct GeneralizedTime;

asn1_tagged!(GeneralizedTime, tag_of!(GENERALIZED_TIME));

impl SpecCombinator for GeneralizedTime {
    type Type = GeneralizedTimeValueInner;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        LengthWrapped(GeneralizedTimeInner).spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        LengthWrapped(GeneralizedTimeInner).spec_serialize(v)
    }
}

impl SecureSpecCombinator for GeneralizedTime {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        LengthWrapped(GeneralizedTimeInner).theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        LengthWrapped(GeneralizedTimeInner).theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        LengthWrapped(GeneralizedTimeInner).lemma_prefix_secure(s1, s2);
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GeneralizedTime {
    type Type = GeneralizedTimeValueInner;
    type SType = GeneralizedTimeValueInner;

    fn length(&self, v: Self::SType) -> usize {
        LengthWrapped(GeneralizedTimeInner).length(v)
    }

    #[inline(always)]
    fn parse(&self, v: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        LengthWrapped(GeneralizedTimeInner).parse(v)
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        LengthWrapped(GeneralizedTimeInner).serialize(v, data, pos)
    }
}

#[derive(Debug, View)]
pub struct GeneralizedTimeInner;

impl SpecCombinator for GeneralizedTimeInner {
    type Type = GeneralizedTimeValueInner;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, v: Seq<u8>) -> Option<(int, Self::Type)> {
        spec_let_some!(
            year = four_chars_to_u16(v[0], v[1], v[2], v[3]);
            month = two_chars_to_u8(v[4], v[5]);
            day = two_chars_to_u8(v[6], v[7]);
            hour = two_chars_to_u8(v[8], v[9]);

            // TODO: this doesn't scale well with the proof
            // so currently we just support the case enforced in the X.509 spec
            // which is YYYYMMDDHHMMSSZ
            {{
                /* if v.len() == 10 {
                    Some((v.len() as int, GeneralizedTimeValueInner {
                        year: year,
                        month: month,
                        day: day,
                        hour: hour,
                        minute: OptionDeep::None,
                        second: OptionDeep::None,
                        fraction: OptionDeep::None,
                        time_zone: GeneralizedTimeZone::Local,
                    }))
                } else if v.len() == 12 {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::None,
                            fraction: OptionDeep::None,
                            time_zone: GeneralizedTimeZone::Local,
                        })) }}
                    )
                } else if v.len() == 14 {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        second = two_chars_to_u8(v[12], v[13]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::Some(second),
                            fraction: OptionDeep::None,
                            time_zone: GeneralizedTimeZone::Local,
                        })) }}
                    )
                } else if v.len() == 18 && v[14] == '.' as u8 {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        second = two_chars_to_u8(v[12], v[13]);
                        fraction = four_chars_to_u16(zero_char!(), v[15], v[16], v[17]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::Some(second),
                            fraction: OptionDeep::Some(fraction),
                            time_zone: GeneralizedTimeZone::Local,
                        })) }}
                    )
                } else if v.len() == 11 && v[10] == 'Z' as u8 {
                    Some((v.len() as int, GeneralizedTimeValueInner {
                        year: year,
                        month: month,
                        day: day,
                        hour: hour,
                        minute: OptionDeep::None,
                        second: OptionDeep::None,
                        fraction: OptionDeep::None,
                        time_zone: GeneralizedTimeZone::UTC,
                    }))
                } else if v.len() == 13 && v[12] == 'Z' as u8 {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::None,
                            fraction: OptionDeep::None,
                            time_zone: GeneralizedTimeZone::UTC,
                        })) }}
                    )
                } else */ if v.len() == 15 && v[14] == 'Z' as u8 {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        second = two_chars_to_u8(v[12], v[13]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::Some(second),
                            fraction: OptionDeep::None,
                            time_zone: GeneralizedTimeZone::UTC,
                        })) }}
                    )
                } /* else if v.len() == 19 && v[14] == '.' as u8 && v[18] == 'Z' as u8 {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        second = two_chars_to_u8(v[12], v[13]);
                        fraction = four_chars_to_u16(zero_char!(), v[15], v[16], v[17]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::Some(second),
                            fraction: OptionDeep::Some(fraction),
                            time_zone: GeneralizedTimeZone::UTC,
                        })) }}
                    )
                } else if v.len() == 15 && (v[v.len() - 5] == '+' as u8 || v[v.len() - 5] == '-' as u8) {
                    spec_let_some!(
                        off_hour = two_chars_to_u8(v[11], v[12]);
                        off_minute = two_chars_to_u8(v[13], v[14]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::None,
                            second: OptionDeep::None,
                            fraction: OptionDeep::None,
                            time_zone: if v[v.len() - 5] == '+' as u8 {
                                GeneralizedTimeZone::UTCPlus(off_hour, off_minute)
                            } else {
                                GeneralizedTimeZone::UTCMinus(off_hour, off_minute)
                            },
                        })) }}
                    )
                } else if v.len() == 17 && (v[v.len() - 5] == '+' as u8 || v[v.len() - 5] == '-' as u8) {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        off_hour = two_chars_to_u8(v[13], v[14]);
                        off_minute = two_chars_to_u8(v[15], v[16]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::None,
                            fraction: OptionDeep::None,
                            time_zone: if v[v.len() - 5] == '+' as u8 {
                                GeneralizedTimeZone::UTCPlus(off_hour, off_minute)
                            } else {
                                GeneralizedTimeZone::UTCMinus(off_hour, off_minute)
                            },
                        })) }}
                    )
                } else if v.len() == 19 && (v[v.len() - 5] == '+' as u8 || v[v.len() - 5] == '-' as u8) {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        second = two_chars_to_u8(v[12], v[13]);
                        off_hour = two_chars_to_u8(v[15], v[16]);
                        off_minute = two_chars_to_u8(v[17], v[18]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::Some(second),
                            fraction: OptionDeep::None,
                            time_zone: if v[v.len() - 5] == '+' as u8 {
                                GeneralizedTimeZone::UTCPlus(off_hour, off_minute)
                            } else {
                                GeneralizedTimeZone::UTCMinus(off_hour, off_minute)
                            },
                        })) }}
                    )
                } else if v.len() == 23 && v[14] == '.' as u8 && (v[v.len() - 5] == '+' as u8 || v[v.len() - 5] == '-' as u8) {
                    spec_let_some!(
                        minute = two_chars_to_u8(v[10], v[11]);
                        second = two_chars_to_u8(v[12], v[13]);
                        fraction = four_chars_to_u16(zero_char!(), v[15], v[16], v[17]);
                        off_hour = two_chars_to_u8(v[19], v[20]);
                        off_minute = two_chars_to_u8(v[21], v[22]);

                        {{ Some((v.len() as int, GeneralizedTimeValueInner {
                            year: year,
                            month: month,
                            day: day,
                            hour: hour,
                            minute: OptionDeep::Some(minute),
                            second: OptionDeep::Some(second),
                            fraction: OptionDeep::Some(fraction),
                            time_zone: if v[v.len() - 5] == '+' as u8 {
                                GeneralizedTimeZone::UTCPlus(off_hour, off_minute)
                            } else {
                                GeneralizedTimeZone::UTCMinus(off_hour, off_minute)
                            },
                        })) }}
                    )
                } */ else {
                    None
                }
            }}
        )
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        spec_let_some!(
            year = u16_to_four_chars(v.year);
            month = u8_to_two_chars(v.month);
            day = u8_to_two_chars(v.day);
            hour = u8_to_two_chars(v.hour);

            {{
                let prefix = seq![
                    year.0, year.1, year.2, year.3,
                    month.0, month.1,
                    day.0, day.1,
                    hour.0, hour.1,
                ];

                match (v.minute, v.second, v.fraction, v.time_zone) {
                    // (OptionDeep::None, OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::Local) => {
                    //     Ok(prefix)
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::Local) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         {{ Ok(prefix + seq![minute.0, minute.1]) }}
                    //     )
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::None, GeneralizedTimeZone::Local) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         second = u8_to_two_chars(second);
                    //         {{ Ok(prefix + seq![minute.0, minute.1, second.0, second.1]) }}
                    //     )
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::Some(fraction), GeneralizedTimeZone::Local) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         second = u8_to_two_chars(second);
                    //         fraction = u16_to_four_chars(fraction);
                    //         {{
                    //             if fraction.0 == zero_char!() {
                    //                 Ok(prefix + seq![minute.0, minute.1, second.0, second.1, '.' as u8, fraction.1, fraction.2, fraction.3])
                    //             } else {
                    //                 Err(())
                    //             }
                    //         }}
                    //     )
                    // },

                    // (OptionDeep::None, OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::UTC) => {
                    //     Ok(prefix + seq!['Z' as u8])
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::UTC) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         {{ Ok(prefix + seq![minute.0, minute.1, 'Z' as u8]) }}
                    //     )
                    // },

                    (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::None, GeneralizedTimeZone::UTC) => {
                        spec_let_some!(
                            minute = u8_to_two_chars(minute);
                            second = u8_to_two_chars(second);
                            {{ Some(prefix + seq![minute.0, minute.1, second.0, second.1, 'Z' as u8]) }}
                        )
                    },

                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::Some(fraction), GeneralizedTimeZone::UTC) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         second = u8_to_two_chars(second);
                    //         fraction = u16_to_four_chars(fraction);
                    //         {{
                    //             if fraction.0 == zero_char!() {
                    //                 seq![minute.0, minute.1, second.0, second.1, '.' as u8, fraction.1, fraction.2, fraction.3, 'Z' as u8]
                    //             } else {
                    //                 seq![]
                    //             }
                    //         }}
                    //     )
                    // },

                    // (OptionDeep::None, OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::UTCPlus(off_hour, off_minute)) |
                    // (OptionDeep::None, OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::UTCMinus(off_hour, off_minute)) => {
                    //     spec_let_some!(
                    //         off_hour = u8_to_two_chars(off_hour);
                    //         off_minute = u8_to_two_chars(off_minute);
                    //         {{ seq![
                    //             if let GeneralizedTimeZone::UTCPlus(..) = v.time_zone {
                    //                 '+' as u8
                    //             } else {
                    //                 '-' as u8
                    //             },
                    //             off_hour.0, off_hour.1,
                    //             off_minute.0, off_minute.1,
                    //         ] }}
                    //     )
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::UTCPlus(off_hour, off_minute)) |
                    // (OptionDeep::Some(minute), OptionDeep::None, OptionDeep::None, GeneralizedTimeZone::UTCMinus(off_hour, off_minute)) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         off_hour = u8_to_two_chars(off_hour);
                    //         off_minute = u8_to_two_chars(off_minute);
                    //         {{ seq![
                    //             if let GeneralizedTimeZone::UTCPlus(..) = v.time_zone {
                    //                 '+' as u8
                    //             } else {
                    //                 '-' as u8
                    //             },
                    //             minute.0, minute.1,
                    //             off_hour.0, off_hour.1,
                    //             off_minute.0, off_minute.1,
                    //         ] }}
                    //     )
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::None, GeneralizedTimeZone::UTCPlus(off_hour, off_minute)) |
                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::None, GeneralizedTimeZone::UTCMinus(off_hour, off_minute)) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         second = u8_to_two_chars(second);
                    //         off_hour = u8_to_two_chars(off_hour);
                    //         off_minute = u8_to_two_chars(off_minute);
                    //         {{ seq![
                    //             if let GeneralizedTimeZone::UTCPlus(..) = v.time_zone {
                    //                 '+' as u8
                    //             } else {
                    //                 '-' as u8
                    //             },
                    //             minute.0, minute.1,
                    //             second.0, second.1,
                    //             off_hour.0, off_hour.1,
                    //             off_minute.0, off_minute.1,
                    //         ] }}
                    //     )
                    // },

                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::Some(fraction), GeneralizedTimeZone::UTCPlus(off_hour, off_minute)) |
                    // (OptionDeep::Some(minute), OptionDeep::Some(second), OptionDeep::Some(fraction), GeneralizedTimeZone::UTCMinus(off_hour, off_minute)) => {
                    //     spec_let_some!(
                    //         minute = u8_to_two_chars(minute);
                    //         second = u8_to_two_chars(second);
                    //         fraction = u16_to_four_chars(fraction);
                    //         off_hour = u8_to_two_chars(off_hour);
                    //         off_minute = u8_to_two_chars(off_minute);
                    //         {{ seq![
                    //             if let GeneralizedTimeZone::UTCPlus(..) = v.time_zone {
                    //                 '+' as u8
                    //             } else {
                    //                 '-' as u8
                    //             },
                    //             minute.0, minute.1,
                    //             second.0, second.1,
                    //             '.' as u8, fraction.1, fraction.2, fraction.3,
                    //             off_hour.0, off_hour.1,
                    //             off_minute.0, off_minute.1,
                    //         ] }}
                    //     )
                    // },

                    _ => Some(seq![]),
                }
            }}
        ).unwrap_or(seq![])
    }
}

impl SecureSpecCombinator for GeneralizedTimeInner {
    closed spec fn is_prefix_secure() -> bool {
        false
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let buf = self.spec_serialize(v);
        if buf.len() > 0 {
            broadcast use
                lemma_two_chars_to_u8_iso, lemma_u8_to_two_chars_iso,
                lemma_four_chars_to_u16_iso, lemma_u16_to_four_chars_iso;
            if let Some((_, v2)) = self.spec_parse(buf) {
                assert(v2 =~= v);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((len, v)) = self.spec_parse(buf) {
            broadcast use
                lemma_two_chars_to_u8_iso, lemma_u8_to_two_chars_iso,
                lemma_four_chars_to_u16_iso, lemma_u16_to_four_chars_iso;
            let ser = self.spec_serialize(v);
            assert(ser =~= buf);
            assert(buf.subrange(0, len) =~= buf);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}


impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GeneralizedTimeInner {
    type Type = GeneralizedTimeValueInner;
    type SType = GeneralizedTimeValueInner;

    fn length(&self, _v: Self::SType) -> usize {
        15
    }

    fn parse(&self, v: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        if v.len() != 15 {
            return Err(ParseError::Other("Invalid or unsupported GeneralizedTime".to_string()));
        }

        let_some!(
            ParseError::Other("Invalid or unsupported GeneralizedTime".to_string()),
            year = four_chars_to_u16(v[0], v[1], v[2], v[3]);
            month = two_chars_to_u8(v[4], v[5]);
            day = two_chars_to_u8(v[6], v[7]);
            hour = two_chars_to_u8(v[8], v[9]);
            minute = two_chars_to_u8(v[10], v[11]);
            second = two_chars_to_u8(v[12], v[13]);

            {{
                if v[14] == 'Z' as u8 {
                    Ok((15, GeneralizedTimeValueInner {
                        year: year,
                        month: month,
                        day: day,
                        hour: hour,
                        minute: OptionDeep::Some(minute),
                        second: OptionDeep::Some(second),
                        fraction: OptionDeep::None,
                        time_zone: GeneralizedTimeZone::UTC,
                    }))
                } else {
                    Err(ParseError::Other("Invalid or unsupported GeneralizedTime".to_string()))
                }
            }}
        )
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let res = let_some!(
            SerializeError::Other("Invalid or unsupported GeneralizedTime".to_string()),

            year = u16_to_four_chars(v.year);
            month = u8_to_two_chars(v.month);
            day = u8_to_two_chars(v.day);
            hour = u8_to_two_chars(v.hour);
            minute = if let OptionDeep::Some(minute) = v.minute { u8_to_two_chars(minute) } else { None };
            second = if let OptionDeep::Some(second) = v.second { u8_to_two_chars(second) } else { None };

            {{
                if let (OptionDeep::None, GeneralizedTimeZone::UTC) = (v.fraction, v.time_zone) {} else {
                    return Err(SerializeError::Other("Unsupported GeneralizedTime".to_string()));
                }

                if pos <= usize::MAX - 15 && pos + 15 <= data.len() {
                    data.set(pos, year.0); data.set(pos + 1, year.1); data.set(pos + 2, year.2); data.set(pos + 3, year.3);
                    data.set(pos + 4, month.0); data.set(pos + 5, month.1);
                    data.set(pos + 6, day.0); data.set(pos + 7, day.1);
                    data.set(pos + 8, hour.0); data.set(pos + 9, hour.1);
                    data.set(pos + 10, minute.0); data.set(pos + 11, minute.1);
                    data.set(pos + 12, second.0); data.set(pos + 13, second.1);
                    data.set(pos + 14, 'Z' as u8);
                    Ok(15)
                } else {
                    Err(SerializeError::InsufficientBuffer)
                }
            }}
        );

        if res.is_ok() {
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@)));
        }

        res
    }
}

/// Conversion between u8 (< 100) and two ASCII chars
#[verifier::opaque]
pub closed spec fn spec_four_chars_to_u16(b1: u8, b2: u8, b3: u8, b4: u8) -> Option<u16> {
    if b1 >= zero_char!() && b1 <= nine_char!() &&
       b2 >= zero_char!() && b2 <= nine_char!() &&
       b3 >= zero_char!() && b3 <= nine_char!() &&
       b4 >= zero_char!() && b4 <= nine_char!() {
        Some(((b1 - zero_char!()) * 1000 + (b2 - zero_char!()) * 100 + (b3 - zero_char!()) * 10 + (b4 - zero_char!())) as u16)
    } else {
        None
    }
}

#[verifier::opaque]
pub closed spec fn spec_u16_to_four_chars(v: u16) -> Option<(u8, u8, u8, u8)> {
    if v >= 10000 {
        None
    } else {
        let b1 = v / 1000;
        let b2 = (v / 100) % 10;
        let b3 = (v / 10) % 10;
        let b4 = v % 10;

        Some(((b1 + zero_char!()) as u8, (b2 + zero_char!()) as u8, (b3 + zero_char!()) as u8, (b4 + zero_char!()) as u8))
    }
}

broadcast proof fn lemma_four_chars_to_u16_iso(b1: u8, b2: u8, b3: u8, b4: u8)
    ensures
        #[trigger] spec_four_chars_to_u16(b1, b2, b3, b4) matches Some(v) ==> {
            &&& 0 <= v < 10000
            &&& spec_u16_to_four_chars(v) matches Some(r)
            &&& r == (b1, b2, b3, b4)
        }
{
    let a = b1 - zero_char!();
    let b = b2 - zero_char!();
    let c = b3 - zero_char!();
    let d = b4 - zero_char!();

    assert(0 <= a <= 9 && 0 <= b <= 9 && 0 <= c <= 9 && 0 <= d <= 9 ==> {
        let r = a * 1000 + b * 100 + c * 10 + d;
        &&& 0 <= r < 10000
        &&& r / 1000 == a
        &&& (r / 100) % 10 == b
        &&& (r / 10) % 10 == c
        &&& r % 10 == d
    }) by (nonlinear_arith);

    reveal(spec_four_chars_to_u16);
    reveal(spec_u16_to_four_chars);
}

broadcast proof fn lemma_u16_to_four_chars_iso(v: u16)
    ensures
        #[trigger] spec_u16_to_four_chars(v) matches Some((b1, b2, b3, b4)) ==> {
            &&& spec_four_chars_to_u16(b1, b2, b3, b4) matches Some(a)
            &&& a == v
        },
        spec_u16_to_four_chars(v).is_none() <==> v >= 10000
{
    assert(v < 10000 ==> {
        let a = v / 1000;
        let b = (v / 100) % 10;
        let c = (v / 10) % 10;
        let d = v % 10;
        &&& a * 1000 + b * 100 + c * 10 + d == v
        &&& 0 <= a <= 9 && 0 <= b <= 9 && 0 <= c <= 9 && 0 <= d <= 9
    }) by (nonlinear_arith);

    reveal(spec_four_chars_to_u16);
    reveal(spec_u16_to_four_chars);
}

#[verifier::when_used_as_spec(spec_four_chars_to_u16)]
pub fn four_chars_to_u16(b1: u8, b2: u8, b3: u8, b4: u8) -> (res: Option<u16>)
    ensures
        res matches Some(res) ==> {
            &&& spec_four_chars_to_u16(b1, b2, b3, b4) matches Some(res2)
            &&& res == res2
        },
        res.is_none() ==> spec_four_chars_to_u16(b1, b2, b3, b4).is_none()
{
    reveal(spec_four_chars_to_u16);
    if b1 >= zero_char!() && b1 <= nine_char!() &&
       b2 >= zero_char!() && b2 <= nine_char!() &&
       b3 >= zero_char!() && b3 <= nine_char!() &&
       b4 >= zero_char!() && b4 <= nine_char!() {
        Some(((b1 - zero_char!()) as u16 * 1000 + (b2 - zero_char!()) as u16 * 100 + (b3 - zero_char!()) as u16 * 10 + (b4 - zero_char!()) as u16) as u16)
    } else {
        None
    }
}

#[verifier::when_used_as_spec(spec_u16_to_four_chars)]
pub fn u16_to_four_chars(v: u16) -> (res: Option<(u8, u8, u8, u8)>)
    ensures
        res matches Some(res) ==> {
            &&& spec_u16_to_four_chars(v) matches Some(res2)
            &&& res2 == res
        },
        res.is_none() ==> spec_u16_to_four_chars(v).is_none(),
{
    reveal(spec_u16_to_four_chars);
    if v >= 10000 {
        None
    } else {
        let b1 = v / 1000;
        let b2 = (v / 100) % 10;
        let b3 = (v / 10) % 10;
        let b4 = v % 10;

        Some((b1 as u8 + zero_char!(), b2 as u8 + zero_char!(), b3 as u8 + zero_char!(), b4 as u8 + zero_char!()))
    }
}

}
