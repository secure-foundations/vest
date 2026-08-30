.PHONY: generate test verify

generate:
	cargo run --manifest-path ../Cargo.toml -p vest_asn1 -- fixture.asn1 -o src/generated.rs
	cargo run --manifest-path ../Cargo.toml -p vest_asn1 -- --rules ber fixture_ber.asn1 -o src/generated_ber.rs
	cargo run --manifest-path ../Cargo.toml -p vest_asn1 -- --rules ber \
		--der-definition Shared \
		--der-definition Canonical \
		--der-definition Ordered \
		fixture_mixed.asn1 -o src/generated_mixed.rs
	cargo run --manifest-path ../Cargo.toml -p vest_asn1 -- --rules ber \
		schema_depth.asn1 -o src/generated_stress_depth.rs
	cargo run --manifest-path ../Cargo.toml -p vest_asn1 -- --rules ber \
		schema_width.asn1 -o src/generated_stress_width.rs
# CMS is a BER envelope around a DER island.  BER is the default because RFC 5652
# section 1 designs every content type for "single pass processing using
# indefinite-length Basic Encoding Rules".  Each DER override below is a
# structure whose octets are a signature or digest input, so a parser that must
# not re-encode has to receive it already in DER:
#
#   SignedAttributes       RFC 5652 5.3   "MUST be DER encoded, even if the rest
#   AuthAttributes         RFC 5652 9.1    of the structure is BER encoded"
#   Certificate            RFC 5280 4.1.1.3 signature is over the DER tbsCertificate;
#                          RFC 5755 7.3   "the DER encoding of the entire PKC"
#   CertificateList        RFC 5280 5.1.1.3 signature is over the DER tbsCertList
#   AttributeCertificate   RFC 5755 7.3   same signed-object shape
#   AttributeCertificateV1 RFC 5652 12.2  same signed-object shape
#
# The rule propagates to every transitive child, which is what puts the whole
# X.509 subtree (AlgorithmIdentifier, Name, Extensions, GeneralName, ORAddress,
# PersonalName, ...) and Attribute/AttributeValue under DER.  ExtendedCertificate
# is deliberately NOT overridden: its closure reaches UnauthAttributes, which CMS
# leaves BER, and RFC 5652 section 10.2.2 declares PKCS #6 extended certificates
# obsolete.  See ../vest_asn1/rfcs/README.md for the full derivation.
	cargo run --manifest-path ../Cargo.toml -p vest_asn1 -- --rules ber \
		--der-definition SignedAttributes \
		--der-definition AuthAttributes \
		--der-definition Certificate \
		--der-definition CertificateList \
		--der-definition AttributeCertificate \
		--der-definition AttributeCertificateV1 \
		../vest_asn1/rfcs/CMS-RFC5652-Curated.asn1 -o src/generated_cms.rs

test: generate
	cargo test

# schema_width.asn1 is a deliberate scalability probe: a 16-field BER SEQUENCE
# cycling OPTIONAL, DEFAULT, and required components.  Its nominal exec proof
# needs more SMT budget than the Verus default, so this crate raises the ceiling.
# Everything else here verifies well inside the default limit.  --rlimit is a
# resource ceiling, not a soundness setting.  Keep this value in step with the
# `vest-asn1-tests` entry in .github/workflows/ci.yml.
VERUS_ARGS := --expand-errors --rlimit 100

verify: generate
	touch src/lib.rs
	cargo verus verify -- $(VERUS_ARGS)
