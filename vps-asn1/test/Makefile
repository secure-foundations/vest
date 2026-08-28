.PHONY: generate test verify

generate:
	cargo run --manifest-path ../Cargo.toml -- fixture.asn1 -o src/generated.rs
	cargo run --manifest-path ../Cargo.toml -- --rules ber fixture_ber.asn1 -o src/generated_ber.rs

test: generate
	cargo test

verify: generate
	touch src/lib.rs
	cargo verus verify -- --expand-errors
