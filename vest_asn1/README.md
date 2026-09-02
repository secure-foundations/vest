# `vest_asn1`

`vest_asn1` generates verified DER and BER parsers and serializers from ASN.1 modules.
The generated codecs use `vest_lib`'s ASN.1 primitives and combinators to achieve compositional specifications, proofs, and executable implementations.

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

Documentation:

- [ASN.1 frontend guide](https://secure-foundations.github.io/vest/guide/asn1/)
- [DER, BER, and rule overrides](https://secure-foundations.github.io/vest/guide/asn1/#der-ber-and-rule-overrides)
- [Generated Rust code](https://secure-foundations.github.io/vest/guide/asn1/generated-api.html)
- [Supported ASN.1 and limitations](https://secure-foundations.github.io/vest/guide/asn1/support.html)
- [`vest_lib::asn1` backend API](https://secure-foundations.github.io/vest/vest_lib/asn1/)
