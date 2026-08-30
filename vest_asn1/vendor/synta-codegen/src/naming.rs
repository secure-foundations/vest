//! Identifier naming helpers shared across code generators.
//!
//! The Rust codegen (`codegen.rs`) has its own copies that additionally
//! handle Rust keyword escaping and differ slightly in capitalisation
//! heuristics — those are intentionally kept separate.

/// Convert an ASN.1 identifier to PascalCase for use as a C type name.
///
/// Each segment (separated by `-` or `_`) is capitalised independently.
/// All-caps segments (every letter character is uppercase) have their
/// non-first letters lowercased, so `KDC-REQ` becomes `KdcReq` rather than
/// `KDCREQ`.  Mixed-case segments such as `Kerberos` are left unchanged.
pub(crate) fn to_pascal_case(s: &str) -> String {
    s.split(['-', '_']).map(pascal_segment).collect()
}

/// Capitalise one separator-delimited segment for PascalCase output.
fn pascal_segment(seg: &str) -> String {
    if seg.is_empty() {
        return String::new();
    }
    let all_caps = seg.chars().all(|c| !c.is_alphabetic() || c.is_uppercase());
    let mut out = String::with_capacity(seg.len());
    for (i, c) in seg.chars().enumerate() {
        if i == 0 {
            out.push(c.to_ascii_uppercase());
        } else if all_caps && c.is_alphabetic() {
            out.push(c.to_ascii_lowercase());
        } else {
            out.push(c);
        }
    }
    out
}

/// Convert an ASN.1 identifier to snake_case for use as a C function name.
pub(crate) fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut prev_was_upper = false;

    for (i, c) in s.chars().enumerate() {
        if c == '-' {
            result.push('_');
            prev_was_upper = false;
        } else if c.is_uppercase() {
            if i > 0 && !prev_was_upper {
                result.push('_');
            }
            result.push(c.to_ascii_lowercase());
            prev_was_upper = true;
        } else {
            result.push(c);
            prev_was_upper = false;
        }
    }

    result
}

/// Convert an ASN.1 identifier to SCREAMING_SNAKE_CASE for C enum constants.
pub(crate) fn to_screaming_snake_case(s: &str) -> String {
    to_snake_case(s).to_uppercase()
}

/// Return a filesystem-safe stem for the given module name.
///
/// Converts PascalCase or ALLCAPS module names to lowercase `snake_case`,
/// e.g. `Certificate` → `certificate`, `RFC5280` → `rfc5280`,
/// `AlgorithmIdentifier` → `algorithm_identifier`.
///
/// The stem is suitable for use as a base filename with any extension.
pub fn module_file_stem(name: &str) -> String {
    let mut out = String::with_capacity(name.len() + 4);
    let mut prev_was_upper = true;
    for c in name.chars() {
        if c.is_uppercase() {
            if !prev_was_upper && !out.is_empty() {
                out.push('_');
            }
            out.extend(c.to_lowercase());
            prev_was_upper = true;
        } else if c.is_alphanumeric() {
            out.push(c);
            prev_was_upper = false;
        } else {
            if !out.ends_with('_') && !out.is_empty() {
                out.push('_');
            }
            prev_was_upper = true;
        }
    }
    out.trim_end_matches('_').to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("test"), "Test");
        assert_eq!(to_pascal_case("test-name"), "TestName");
        assert_eq!(to_pascal_case("test_name"), "TestName");
        assert_eq!(to_pascal_case("myType"), "MyType");
    }

    #[test]
    fn test_to_pascal_case_all_caps_segments() {
        // All-caps segments: each gets first-letter-upper, rest lower
        assert_eq!(to_pascal_case("KDC-REQ"), "KdcReq");
        assert_eq!(to_pascal_case("KDC-REQ-BODY"), "KdcReqBody");
        assert_eq!(to_pascal_case("KRB-ERROR"), "KrbError");
        assert_eq!(to_pascal_case("AP-REQ"), "ApReq");
        assert_eq!(to_pascal_case("PA-DATA"), "PaData");
        assert_eq!(to_pascal_case("TGS-REP"), "TgsRep");
        assert_eq!(to_pascal_case("KRB-SAFE-BODY"), "KrbSafeBody");
    }

    #[test]
    fn test_to_pascal_case_mixed_case_preserved() {
        // Mixed-case segments (already have lowercase letters) are left as-is
        assert_eq!(to_pascal_case("KerberosString"), "KerberosString");
        assert_eq!(to_pascal_case("AlgorithmIdentifier"), "AlgorithmIdentifier");
        assert_eq!(to_pascal_case("EncKDCRepPart"), "EncKDCRepPart");
    }

    #[test]
    fn test_to_pascal_case_digits_in_segment() {
        // Digits are neutral — they don't affect the all-caps determination
        assert_eq!(to_pascal_case("ETYPE-INFO2"), "EtypeInfo2");
        assert_eq!(to_pascal_case("ETYPE-INFO2-ENTRY"), "EtypeInfo2Entry");
        assert_eq!(to_pascal_case("PA-ENC-TS-ENC"), "PaEncTsEnc");
    }

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("Test"), "test");
        assert_eq!(to_snake_case("TestName"), "test_name");
        assert_eq!(to_snake_case("test-name"), "test_name");
        assert_eq!(to_snake_case("camelCase"), "camel_case");
    }

    #[test]
    fn test_to_screaming_snake_case() {
        assert_eq!(to_screaming_snake_case("Test"), "TEST");
        assert_eq!(to_screaming_snake_case("TestName"), "TEST_NAME");
        assert_eq!(to_screaming_snake_case("test-name"), "TEST_NAME");
    }

    #[test]
    fn test_stem_pascal_case() {
        assert_eq!(module_file_stem("Certificate"), "certificate");
        assert_eq!(
            module_file_stem("AlgorithmIdentifier"),
            "algorithm_identifier"
        );
    }

    #[test]
    fn test_stem_all_caps() {
        assert_eq!(module_file_stem("RFC5280"), "rfc5280");
    }

    #[test]
    fn test_stem_single_word() {
        assert_eq!(module_file_stem("PKIX"), "pkix");
        assert_eq!(module_file_stem("Kerberos"), "kerberos");
    }
}
