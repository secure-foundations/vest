#![allow(warnings)]

pub mod generated_ber;
pub mod generated_cms_ber;
pub mod generated_cms_der;
pub mod generated_der;

#[cfg(test)]
mod real_cms_tests {
    use super::generated_cms_der;
    use vest_lib2::core::exec::Parser;

    fn body(input: &[u8], offset: usize) -> (&[u8], usize) {
        let first = input[offset + 1];
        if first < 0x80 {
            (&input[offset + 2..offset + 2 + first as usize], offset + 2)
        } else {
            let count = (first & 0x7f) as usize;
            let mut len = 0usize;
            for byte in &input[offset + 2..offset + 2 + count] {
                len = (len << 8) | *byte as usize;
            }
            let start = offset + 2 + count;
            (&input[start..start + len], start)
        }
    }

    fn signed_data(input: &[u8]) -> &[u8] {
        let (sequence, sequence_start) = body(input, 0);
        let (_, oid_start) = body(input, sequence_start);
        let explicit_offset = oid_start + sequence[1] as usize;
        let (explicit, _) = body(input, explicit_offset);
        explicit
    }

    #[test]
    fn generated_schema_accepts_rustcrypto_pkits_signed_data() {
        for input in [
            include_bytes!("../../../corpora/cms/pkits.p7b").as_slice(),
            include_bytes!("../../../corpora/cms/pkits_ee.p7b").as_slice(),
        ] {
            let signed = signed_data(input);
            let (consumed, _) = generated_cms_der::SIGNED_DATA::Fmt
                .parse(&&signed[..])
                .unwrap();
            assert_eq!(consumed, signed.len());
        }
    }
}
