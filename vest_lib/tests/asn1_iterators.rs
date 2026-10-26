//! Iterator validation, range constraints, and checked INTEGER conversion.

use vest_lib::asn1::bmpstring::check_valid_bmp_string;
use vest_lib::asn1::constraints::{IntegerRange, Size};
use vest_lib::asn1::datetime::is_digits;
use vest_lib::asn1::ia5string::is_valid_ia5_string;
use vest_lib::asn1::numericstring::is_numeric_string_char;
use vest_lib::asn1::printablestring::{is_printable_byte, is_valid_printable_string};
use vest_lib::asn1::universalstring::check_valid_universal_string;
use vest_lib::asn1::{Integer16Fmt, NumericStringFmt};
use vest_lib::core::exec::fns::Pred;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

#[test]
fn every_bmp_code_unit() {
    for code in 0..=u16::MAX {
        assert_eq!(
            check_valid_bmp_string(&code.to_be_bytes()),
            char::from_u32(u32::from(code)).is_some(),
            "code unit {code:#x}"
        );
    }
    assert!(check_valid_bmp_string(&[]));
    assert!(!check_valid_bmp_string(&[0]));
    assert!(!check_valid_bmp_string(&[0, b'A', 0]));
    assert!(!check_valid_bmp_string(&[0, b'A', 0xd8, 0, 0, b'B']));
}

#[test]
fn every_unicode_code_point() {
    for code in 0u32..=0x110000 {
        assert_eq!(
            check_valid_universal_string(&code.to_be_bytes()),
            char::from_u32(code).is_some(),
            "code point {code:#x}"
        );
    }
    assert!(check_valid_universal_string(&[]));
    assert!(!check_valid_universal_string(&u32::MAX.to_be_bytes()));
    for length in 1..4 {
        assert!(!check_valid_universal_string(&[0; 4][..length]));
    }
    assert!(!check_valid_universal_string(&[
        0, 0, 0, b'A', 0, 0, 0xd8, 0
    ]));
}

#[test]
fn ascii_repertoires() {
    assert!(is_valid_ia5_string(&[]));
    assert!(is_valid_printable_string(&[]));
    for byte in 0..=u8::MAX {
        assert_eq!(is_valid_ia5_string(&[byte]), byte.is_ascii());
        let printable = byte.is_ascii_alphanumeric() || b" '()+,-./:=?".contains(&byte);
        assert_eq!(is_printable_byte(byte), printable);
        assert_eq!(is_valid_printable_string(&[byte]), printable);
        assert_eq!(is_valid_printable_string(&[b'A', byte, b'Z']), printable);
        assert_eq!(
            is_numeric_string_char(char::from(byte)),
            byte == b' ' || byte.is_ascii_digit()
        );
    }
}

#[test]
fn inclusive_and_unbounded_constraints() {
    for value in [i16::MIN, -2, -1, 0, 1, 2, i16::MAX] {
        assert_eq!(
            IntegerRange::<true, -1, true, 1>.test(&value),
            (-1..=1).contains(&value)
        );
        assert_eq!(
            IntegerRange::<true, -1, false, -99>.test(&value),
            value >= -1
        );
        assert_eq!(IntegerRange::<false, 99, true, 1>.test(&value), value <= 1);
        assert!(IntegerRange::<false, 99, false, -99>.test(&value));
        assert!(!IntegerRange::<true, 1, true, -1>.test(&value));
    }
    for len in 0..=4 {
        let bytes = &[0u8; 4][..len];
        assert_eq!(
            Size::<true, 1, true, 3>.test(&bytes),
            (1..=3).contains(&len)
        );
        assert_eq!(Size::<true, 1, false, 0>.test(&bytes), len >= 1);
        assert_eq!(Size::<false, 99, true, 3>.test(&bytes), len <= 3);
        assert!(Size::<false, 99, false, 0>.test(&bytes));
        assert!(!Size::<true, 3, true, 1>.test(&bytes));
    }
}

#[test]
fn decimal_spans() {
    for byte in 0..=u8::MAX {
        let bytes = [b'x', byte, b'y'];
        assert_eq!(is_digits(&bytes, 1, 2), byte.is_ascii_digit());
        assert!(!is_digits(&bytes, 0, 3));
        for pos in 0..=bytes.len() {
            assert!(is_digits(&bytes, pos, pos));
        }
    }
    for start in 0..=3 {
        for end in start..=3 {
            assert!(is_digits(b"123", start, end));
        }
    }
}

#[test]
fn numeric_strings() {
    for text in ["", "123 456", &"0123456789 ".repeat(128)] {
        let (n, value) = NumericStringFmt.parse(&text.as_bytes()).unwrap();
        assert_eq!(n, text.len());
        assert_eq!(value.inner(), text);
    }
    for text in ["12+34", "123A", " 0-", "Ω"] {
        assert!(NumericStringFmt.parse(&text.as_bytes()).is_err());
    }
}

#[test]
fn every_integer16_value() {
    for value in i16::MIN..=i16::MAX {
        let length = Integer16Fmt.prepare(&value).unwrap();
        assert_eq!(length, if i8::try_from(value).is_ok() { 1 } else { 2 });
        let mut bytes = [0; 2];
        Integer16Fmt.serialize(&value, &mut bytes[..length]);
        assert_eq!(
            Integer16Fmt.parse(&&bytes[..length]).unwrap(),
            (length, value)
        );
    }
}
