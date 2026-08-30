# ASN.1 frontend

`vest_asn1` parses an ASN.1 module and emits nominal verified formats backed by
`vest_lib::asn1`. DER is the default; BER and definition-level rule overrides
are available.

```console
cargo run -p vest_asn1 -- schema.asn1 -o generated.rs
cargo run -p vest_asn1 -- --rules ber schema.asn1 -o generated_ber.rs
```

Each supported ASN.1 definition becomes a user-facing Rust value type and a
nominal format whose nested combinator implementation is verified once. This
boundary keeps enclosing schemas from repeatedly expanding large combinator
types during verification.

Read [DER, BER, and rule overrides](rules.md) before generating mixed-rule
modules, then see the [generated API](generated-api.md) and
[support table](support.md). The backend API is documented under
[`vest_lib::asn1`](https://secure-foundations.github.io/vest/vest_lib/asn1/).

