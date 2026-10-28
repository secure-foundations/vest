# ASN.1 Compiler

`vest_asn1` parses an ASN.1 module and emits verified formats backed by
`vest_lib::asn1`. DER is the default; BER and definition-level rule overrides
are available.

```console
cargo install vest_asn1 --version 0.1.0 --locked
vest_asn1 schema.asn1 -o generated.rs
vest_asn1 --rules ber schema.asn1 -o generated_ber.rs
```

Version 0.1.0 targets `vest_lib` 0.2.3 and the matching Verus/vstd versions in
the [tutorial](tutorial.md). The compiler emits Rust code with Verus specs and proofs; run Verus
on the generated code to check those proofs.

Similar to the Vest DSL, each supported ASN.1 definition becomes a user-facing Rust value type and a nominal format type whose specification, proof, and executable implementation are all derived from the
inner combinator representation.

Start with the [ASN.1 tutorial](tutorial.md), then see the
[generated Rust code](generated-api.md) and the
[support table](support.md). The backend API is documented under
[`vest_lib::asn1`](../../vest_lib/asn1/).

## DER, BER, and rule overrides

`--rules der` or `--rules ber` authoritatively selects the module default. A
definition override changes that definition and the transitive children it
needs under the selected rule; parents remain under the module default.

```console
vest_asn1 --rules ber \
  --der-definition SignedAttributes \
  --der-definition CertificateSet \
  schema.asn1 -o generated_mixed.rs
```

Every ASN.1 definition is emitted exactly once with one global rule. A BER
definition may contain a DER child because a DER encoding is valid BER. However,
a DER definition cannot depend on a BER definition without violating DER
canonicality. Conflicting transitive overrides are rejected and require an
explicit rule boundary.
