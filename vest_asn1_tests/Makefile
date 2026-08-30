.PHONY: generate test verify

generate:
	cargo run --manifest-path ../vest_asn1/Cargo.toml -- fixture.asn1 -o src/generated.rs
	cargo run --manifest-path ../vest_asn1/Cargo.toml -- --rules ber fixture_ber.asn1 -o src/generated_ber.rs
	cargo run --manifest-path ../vest_asn1/Cargo.toml -- --rules ber \
		--der-definition Shared \
		--der-definition Canonical \
		--der-definition Ordered \
		fixture_mixed.asn1 -o src/generated_mixed.rs
	cargo run --manifest-path ../vest_asn1/Cargo.toml -- --rules ber \
		schema_depth.asn1 -o src/generated_stress_depth.rs
	cargo run --manifest-path ../vest_asn1/Cargo.toml -- --rules ber \
		schema_width.asn1 -o src/generated_stress_width.rs

test: generate
	cargo test

verify: generate
	touch src/lib.rs
	cargo verus verify -- --expand-errors
