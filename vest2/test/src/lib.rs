#![cfg_attr(verus_only, verifier::allow(autoderive_clone_without_spec))]
// #![verifier::allow(autoderive_clone_without_spec)]

pub mod anonymous_nested;
pub mod bitcoin;
pub mod bits;
pub mod bits_little;
// pub mod cbor;
pub mod codegen;
pub mod elab;
pub mod enum_constraints;
pub mod enums;
pub mod josh;
pub mod length_expr;
pub mod matches;
pub mod mutual_rec;
pub mod nested_access;
pub mod nested_bytes;
pub mod opt;
pub mod repeat;
pub mod tls;
pub mod tlv;

#[cfg(test)]
mod serializer_composition_regressions {
    use super::nested_bytes::{
        Anything, NestedDynamicBytes, NestedDynamicBytesFmt, NestedFixedBytes, NestedFixedBytesFmt,
        TailVec, TailVecFmt,
    };
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::{Prepare, SerializerExt};

    #[test]
    fn nested_dynamic_bytes_roundtrip_in_place() {
        let first = [0x10, 0x11, 0x12];
        let second = [0x20, 0x21, 0x22];
        let value = NestedDynamicBytes {
            num: 2,
            num_inner: 3,
            xs: vec![first.as_slice(), second.as_slice()],
        };

        let len = NestedDynamicBytesFmt.prepare(&value).unwrap();
        let mut buf = vec![0; len];
        NestedDynamicBytesFmt.serialize(&value, buf.as_mut_slice());
        let (consumed, parsed) = NestedDynamicBytesFmt.parse(&&buf[..]).unwrap();

        assert_eq!(consumed, buf.len());
        assert_eq!(parsed, value);
    }

    #[test]
    fn nested_fixed_bytes_roundtrip_in_place() {
        let first = [0x31; 10];
        let second = [0x42; 10];
        let value = NestedFixedBytes {
            num: 2,
            xs: vec![first.as_slice(), second.as_slice()],
        };

        let len = NestedFixedBytesFmt.prepare(&value).unwrap();
        let mut buf = vec![0; len];
        NestedFixedBytesFmt.serialize(&value, buf.as_mut_slice());
        let (consumed, parsed) = NestedFixedBytesFmt.parse(&&buf[..]).unwrap();

        assert_eq!(consumed, buf.len());
        assert_eq!(parsed, value);
    }

    #[test]
    fn nested_byte_lengths_are_checked_during_prepare() {
        let chunk = [0xaa, 0xbb, 0xcc];
        let wrong_outer_count = NestedDynamicBytes {
            num: 2,
            num_inner: 3,
            xs: vec![chunk.as_slice()],
        };
        assert!(NestedDynamicBytesFmt.prepare(&wrong_outer_count).is_err());

        let short_chunk = [0xaa, 0xbb];
        let wrong_inner_count = NestedDynamicBytes {
            num: 1,
            num_inner: 3,
            xs: vec![short_chunk.as_slice()],
        };
        assert!(NestedDynamicBytesFmt.prepare(&wrong_inner_count).is_err());
    }

    #[test]
    fn tail_then_vec_roundtrip_in_place() {
        let value = TailVec {
            xs: vec![Anything { x: 1 }, Anything { x: 2 }, Anything { x: 3 }],
        };

        let len = TailVecFmt.prepare(&value).unwrap();
        let mut buf = vec![0; len];
        TailVecFmt.serialize(&value, buf.as_mut_slice());
        let (consumed, parsed) = TailVecFmt.parse(&&buf[..]).unwrap();

        assert_eq!(consumed, buf.len());
        assert_eq!(parsed, value);
    }
}

#[cfg(test)]
mod bits_endianness_sanity {
    use super::{bits, bits_little};
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::{Prepare, SerializerExt};

    #[test]
    fn version_ihl_is_byte_endian_invariant() {
        let v = bits::VersionIhl { version: 4, ihl: 5 };

        let mut be = vec![0; bits::VersionIhlFmt.prepare(&v).unwrap()];
        bits::VersionIhlFmt.serialize(&v, be.as_mut_slice());
        assert_eq!(be, vec![0x45]);

        let le_v = bits_little::VersionIhl { version: 4, ihl: 5 };
        let mut le = vec![0; bits_little::VersionIhlFmt.prepare(&le_v).unwrap()];
        bits_little::VersionIhlFmt.serialize(&le_v, le.as_mut_slice());
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

        let mut be = vec![0; bits::CrossByteSpanFmt.prepare(&be_v).unwrap()];
        bits::CrossByteSpanFmt.serialize(&be_v, be.as_mut_slice());
        assert_eq!(be, vec![0xAA, 0xAB]);

        let mut le = vec![0; bits_little::CrossByteSpanFmt.prepare(&le_v).unwrap()];
        bits_little::CrossByteSpanFmt.serialize(&le_v, le.as_mut_slice());
        assert_eq!(le, vec![0xAB, 0xAA]);
        assert_ne!(be, le);

        let (_, parsed_be) = bits::CrossByteSpanFmt.parse(&&be[..]).unwrap();
        assert_eq!(parsed_be, be_v);

        let (_, parsed_le) = bits_little::CrossByteSpanFmt.parse(&&le[..]).unwrap();
        assert_eq!(parsed_le, le_v);
    }
}

#[cfg(test)]
mod named_error_sanity {
    use super::nested_access;
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::Prepare;

    #[test]
    fn parse_error_carries_named_format_stack() {
        let input = [0xff, 0xff, 0xff, 0x00];
        let err = nested_access::FinalMsgFmt.parse(&&input[..]).unwrap_err();
        let msg = err.to_string();
        println!("Parse error message: {}", msg);
        assert!(msg.contains("input ended before the format could finish parsing"));
        assert!(msg.contains("`combined_example` -> `generic_header`"));
    }

    #[test]
    fn prepare_error_uses_named_nested_format() {
        let empty: &[u8] = &[];
        let v = nested_access::FinalMsg {
            total_len: 16_777_215,
            body: nested_access::CombinedExample {
                header: nested_access::GenericHeader {
                    next_type: 0,
                    reserved: 0,
                    payload_length: 7,
                },
                body: empty,
            },
            hdr_payload: nested_access::PayloadWithHeader {
                hdr: nested_access::GenericHeader {
                    next_type: 0,
                    reserved: 0,
                    payload_length: 8,
                },
                body: empty,
            },
            nested: nested_access::NestedComplex {
                flag: 0,
                data: empty,
            },
        };

        let err = nested_access::FinalMsgFmt.prepare(&v).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("value failed a refinement predicate"));
        assert!(msg.contains("`combined_example` -> `generic_header`"));
    }
}

#[cfg(test)]
mod tls_error_sanity {
    use super::tls;
    use vest_lib2::combinators::Named;
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::{Prepare, SerializerExt};

    #[test]
    fn pre_shared_key_extension_parse_error_is_semantic_and_deeply_nested() {
        let input = [
            0x00, 0x29, // extension_type = PreSharedKey
            0x00, 0x09, // ext_len = 9
            0x00, 0x07, // psk_identities total length = 7
            0x00, 0x00, // first identity: opaque_1_ffff length = 0, rejected by predicate
            0x00, 0x00, 0x00, 0x00, 0x00, // remaining bytes inside the exact-length chunk
        ];

        let err = Named("client_hello_extension", tls::ClientHelloExtensionFmt)
            .parse(&&input[..])
            .unwrap_err();
        let msg = err.to_string();
        println!("TLS parse error message: {}", msg);
        assert!(msg.contains("a length-delimited parser did not consume the declared length"));
        assert!(msg.contains(
            "`client_hello_extension` -> `client_hello_extension_extension_data` -> `pre_shared_key_client_extension` -> `offered_psks` -> `psk_identities`"
        ));
    }

    #[test]
    fn hello_retry_request_prepare_error_carries_deep_named_stack() {
        let empty: &[u8] = &[];
        let v = tls::HelloRetryRequest {
            legacy_session_id_echo: tls::SessionId { l: 0, id: empty },
            cipher_suite: tls::CipherSuite::TLS_AES_128_GCM_SHA256,
            legacy_compression_method: 0,
            extensions: tls::HelloRetryExtensions {
                l: 6,
                list: vec![tls::HelloRetryExtension {
                    extension_type: tls::ExtensionType::Cookie,
                    ext_len: 2,
                    extension_data: tls::HelloRetryExtensionExtensionData::Cookie(tls::Cookie {
                        l: 0,
                        data: empty,
                    }),
                }],
            },
        };

        let err = tls::HelloRetryRequestFmt.prepare(&v).unwrap_err();
        let msg = err.to_string();
        println!("TLS prepare error message: {}", msg);
        assert!(msg.contains("value failed a refinement predicate"));
        assert!(msg.contains(
            "`hello_retry_extensions` -> `hello_retry_extension_extension_data` -> `cookie` -> `opaque_1_ffff`"
        ));
    }

    #[test]
    fn hello_retry_request_roundtrips_when_well_formed() {
        let cookie_data: &[u8] = &[0xaa];
        let v = tls::HelloRetryRequest {
            legacy_session_id_echo: tls::SessionId { l: 0, id: &[] },
            cipher_suite: tls::CipherSuite::TLS_AES_128_GCM_SHA256,
            legacy_compression_method: 0,
            extensions: tls::HelloRetryExtensions {
                l: 7,
                list: vec![tls::HelloRetryExtension {
                    extension_type: tls::ExtensionType::Cookie,
                    ext_len: 3,
                    extension_data: tls::HelloRetryExtensionExtensionData::Cookie(tls::Cookie {
                        l: 1,
                        data: cookie_data,
                    }),
                }],
            },
        };

        let len = tls::HelloRetryRequestFmt.prepare(&v).unwrap();
        let mut buf = vec![0; len];
        tls::HelloRetryRequestFmt.serialize(&v, buf.as_mut_slice());
        let (_, parsed) = tls::HelloRetryRequestFmt.parse(&&buf[..]).unwrap();
        assert_eq!(parsed, v);
        assert_eq!(tls::HelloRetryRequestFmt.prepare(&v).unwrap(), buf.len());
    }
}

#[cfg(test)]
mod never_error_sanity {
    use super::matches;
    use vest_lib2::core::exec::parser::Parser;

    #[test]
    fn test_never_error_message() {
        let input = [0x02, 0x00, 0x00];
        let err = matches::Msg4Fmt.parse(&&input[..]).unwrap_err();
        let err_msg = err.to_string();
        println!("Never combinator error: {}", err_msg);
        assert!(err_msg.contains("i for msg4 can only be 1"));
    }
}
