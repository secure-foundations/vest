# `vest_asn1`

`vest_asn1` generates DER and BER parsers and serializers from ASN.1 modules.
The generated Rust includes specifications and proofs built on `vest_lib`'s ASN.1 primitives and combinators;
check them with Verus before integrating into your project.
The `vest_asn1` compiler itself is ordinary, unverified Rust.

## Install and generate

```console
cargo install vest_asn1 --version 0.1.0 --locked
vest_asn1 schema.asn1 -o generated.rs
vest_asn1 --rules ber schema.asn1 -o generated_ber.rs
```

For this compiler release, use `vest_lib = "=0.2.3"` and
`vstd = { version = "=0.0.0-2026-10-25-0158", default-features = false }`
in the generated code's project. Verification uses Verus
`0.2026.10.26.d17fbd0` with Rust `1.99.1`. See the
[tutorial](https://secure-foundations.github.io/vest/guide/asn1/tutorial.html)
for a complete project and verification command.

Definitions may override the module rule. Overrides apply to the selected
definition and its required transitive children while parents retain the
module default:

```console
vest_asn1 --rules ber \
  --der-definition SignedAttributes \
  --der-definition CertificateSet \
  schema.asn1 -o generated_mixed.rs
```

## Documentation

- [ASN.1 frontend guide](https://secure-foundations.github.io/vest/guide/asn1/)
- [DER, BER, and rule overrides](https://secure-foundations.github.io/vest/guide/asn1/#der-ber-and-rule-overrides)
- [Generated Rust code](https://secure-foundations.github.io/vest/guide/asn1/generated-api.html)
- [Supported ASN.1 and limitations](https://secure-foundations.github.io/vest/guide/asn1/support.html)
- [`vest_lib::asn1` backend API](https://secure-foundations.github.io/vest/vest_lib/asn1/)

The schema parser and AST are adapted from Synta; see [third-party notices](THIRD_PARTY.md).
