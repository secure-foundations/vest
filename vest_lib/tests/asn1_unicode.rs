//! Unicode boundaries, malformed contents, and long-string roundtrips.
#![cfg(feature = "alloc")]

use vest_lib::asn1::{BmpStringFmt, UniversalStringFmt};
use vest_lib::core::exec::{ByteLen, Parser, Prepare, Serializer, SerializerExt};

#[test]
fn bmp_string_roundtrip() {
    for text in [
        "",
        "ASCII",
        "\0\u{7f}\u{80}\u{7ff}\u{800}\u{d7ff}\u{e000}\u{ffff}",
        &"AΩ中\u{ffff}".repeat(4096),
    ] {
        let wire: Vec<_> = text
            .chars()
            .flat_map(|c| (c as u16).to_be_bytes())
            .collect();
        let (consumed, value) = BmpStringFmt.parse(&wire.as_slice()).unwrap();
        assert_eq!(consumed, wire.len());
        assert_eq!(value.inner(), text);
        let len = BmpStringFmt.prepare(&value).unwrap();
        assert_eq!(len, BmpStringFmt.length(&value));
        let mut slice_output = vec![0; len];
        BmpStringFmt.serialize(&value, &mut slice_output);
        assert_eq!(slice_output, wire);
        let mut vec_output = vec![0xaa];
        BmpStringFmt.serialize_into(&value, &mut vec_output);
        assert_eq!(vec_output[0], 0xaa);
        assert_eq!(&vec_output[1..], wire);
    }
}

#[test]
fn universal_string_roundtrip() {
    for text in [
        "",
        "ASCII",
        "\0\u{7f}\u{80}\u{7ff}\u{800}\u{d7ff}\u{e000}\u{ffff}\u{10000}\u{10ffff}",
        &"AΩ中😀".repeat(4096),
    ] {
        let wire: Vec<_> = text
            .chars()
            .flat_map(|c| (c as u32).to_be_bytes())
            .collect();
        let (consumed, value) = UniversalStringFmt.parse(&wire.as_slice()).unwrap();
        assert_eq!(consumed, wire.len());
        assert_eq!(value, text);
        let len = UniversalStringFmt.prepare(&value).unwrap();
        assert_eq!(len, UniversalStringFmt.length(&value));
        let mut slice_output = vec![0; len];
        UniversalStringFmt.serialize(&value, &mut slice_output);
        assert_eq!(slice_output, wire);
        let mut vec_output = vec![0xaa];
        UniversalStringFmt.serialize_into(&value, &mut vec_output);
        assert_eq!(vec_output[0], 0xaa);
        assert_eq!(&vec_output[1..], wire);
    }
}

#[test]
fn rejects_non_scalar_code_units() {
    for bytes in [&[0xd8, 0x00][..], &[0xdf, 0xff], &[0x00]] {
        assert!(BmpStringFmt.parse(&bytes).is_err());
    }
    for bytes in [
        &[0, 0, 0xd8, 0][..],
        &[0, 0, 0xdf, 0xff],
        &[0, 0x11, 0, 0],
        &[0xff; 4],
        &[0],
        &[0, 0],
        &[0, 0, 0],
    ] {
        assert!(UniversalStringFmt.parse(&bytes).is_err());
    }
}
