# vest_asn1

`vest_asn1` generates verified nominal DER and BER formats from ASN.1 modules.
The generated codecs use `vest_lib`'s ASN.1 primitives, executable APIs, and
compositional proofs directly. DER is the default.

```console
cargo run -p vest_asn1 -- schema.asn1 -o generated.rs
cargo run -p vest_asn1 -- --rules ber schema.asn1 -o generated_ber.rs
```

Definitions may override the module rule. Overrides apply to the selected
definition and its required transitive children while parents retain the
module default:

```console
cargo run -p vest_asn1 -- --rules ber \
  --der-definition SignedAttributes \
  --der-definition CertificateSet \
  schema.asn1 -o generated_mixed.rs
```

Each ASN.1 definition becomes a Rust value type and a fully verified nominal
format such as `ALGORITHM_IDENTIFIER::Fmt`. Generated structs and enums hide
the backend's nested tuples and sums, and enclosing formats depend on compact
already-proved interfaces.

Documentation:

- [ASN.1 frontend guide](https://secure-foundations.github.io/vest/guide/asn1/)
- [DER, BER, and rule overrides](https://secure-foundations.github.io/vest/guide/asn1/rules.html)
- [Generated API](https://secure-foundations.github.io/vest/guide/asn1/generated-api.html)
- [Supported ASN.1 and limitations](https://secure-foundations.github.io/vest/guide/asn1/support.html)
- [`vest_lib::asn1` backend API](https://secure-foundations.github.io/vest/vest_lib/asn1/)

The checked DER, BER, and mixed-rule fixtures under `vest_asn1_tests` are
regenerated and verified in CI.
