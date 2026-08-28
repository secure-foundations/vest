# VPS ASN.1 compiler

This crate compiles ASN.1 modules into verified VPS formats. DER is the default;
`--rules ber` selects BER.

```sh
cargo run -- schema.asn1 -o generated.rs
cargo run -- --rules ber schema.asn1 -o generated_ber.rs
```

Selected definitions can use the other rule. Overrides also apply to their
children, while enclosing definitions keep the command-line rule:

```sh
cargo run -- --rules ber \
  --der-definition SignedAttributes \
  --der-definition CertificateSet \
  schema.asn1 -o generated_mixed.rs
```

The CMS case study is
[`rfcs/CMS-RFC5652-Curated.asn1`](rfcs/CMS-RFC5652-Curated.asn1).

## Generated code

Each ASN.1 definition becomes a named Rust value type and a fully verified
format. Generated code uses nominal format boundaries so Verus does not expand
an entire schema whenever one definition is reused. The backend proves parsing,
serialization, length calculation, preparation, tagging, disjointness, and the
round-trip properties that apply to the selected encoding rule.

The compiler supports the primitive and string types used by the paper,
SEQUENCE, CHOICE, SEQUENCE OF, SET, SET OF, OPTIONAL, DEFAULT, size and integer
constraints, and context/application/private IMPLICIT and EXPLICIT tags. BER
supports constructed strings and definite or indefinite containers. DER
enforces canonical ordering for SET and SET OF.

## Current limits

- Recursive schema declarations are not yet generated.
- Heterogeneous BER SET is not generated.
- Tag-disjointness automation is exact for tag numbers 0--30. High tag numbers
  with the same class and constructed bit need a future exact fallback.
- RELATIVE-OID, GeneralString, VisibleString, ANY DEFINED BY, BIT STRING size
  constraints, and general constraint combinations are not supported.
- OBJECT IDENTIFIER and REAL constant assignments are not generated.

Unsupported input is rejected with a source path instead of being silently
approximated.

## Test and verify

```sh
cargo test
cd test
make generate
make test
make verify
```
