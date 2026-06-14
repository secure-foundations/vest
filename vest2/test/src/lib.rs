pub mod anonymous_nested;
pub mod bitcoin;
pub mod bits;
pub mod bits_little;
pub mod codegen;
pub mod elab;
pub mod enum_constraints;
pub mod enums;
pub mod josh;
pub mod length_expr;
pub mod matches;
pub mod nested_access;
pub mod opt;
pub mod repeat;
pub mod tls;
pub mod tlv;

#[cfg(test)]
mod bits_endianness_sanity {
    use super::{bits, bits_little};
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::Serializer;

    #[test]
    fn version_ihl_is_byte_endian_invariant() {
        let v = bits::VersionIhl { version: 4, ihl: 5 };

        let mut be = Vec::new();
        bits::VersionIhlFmt.serialize(&v, &mut be);
        assert_eq!(be, vec![0x45]);

        let mut le = Vec::new();
        bits_little::VersionIhlFmt
            .serialize(&bits_little::VersionIhl { version: 4, ihl: 5 }, &mut le);
        assert_eq!(le, vec![0x45]);
        assert_eq!(be, le);

        let (_, parsed_be) = bits::VersionIhlFmt.parse(&&be[..]).unwrap();
        assert_eq!(parsed_be, v);

        let (_, parsed_le) = bits_little::VersionIhlFmt.parse(&&le[..]).unwrap();
        assert_eq!(parsed_le, bits_little::VersionIhl { version: 4, ihl: 5 });
    }

    #[test]
    fn cross_byte_span_differs_by_byte_endianness() {
        let be_v = bits::CrossByteSpan {
            prefix: 5,
            span: 0x155,
            suffix: 3,
        };
        let le_v = bits_little::CrossByteSpan {
            prefix: 5,
            span: 0x155,
            suffix: 3,
        };

        let mut be = Vec::new();
        bits::CrossByteSpanFmt.serialize(&be_v, &mut be);
        assert_eq!(be, vec![0xAA, 0xAB]);

        let mut le = Vec::new();
        bits_little::CrossByteSpanFmt.serialize(&le_v, &mut le);
        assert_eq!(le, vec![0xAB, 0xAA]);
        assert_ne!(be, le);

        let (_, parsed_be) = bits::CrossByteSpanFmt.parse(&&be[..]).unwrap();
        assert_eq!(parsed_be, be_v);

        let (_, parsed_le) = bits_little::CrossByteSpanFmt.parse(&&le[..]).unwrap();
        assert_eq!(parsed_le, le_v);
    }
}
