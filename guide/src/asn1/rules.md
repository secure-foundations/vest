# DER, BER, and rule overrides

`--rules der` or `--rules ber` authoritatively selects the module default. A
definition override changes that definition and the transitive children it
needs under the selected rule; parents remain under the module default.

```console
cargo run -p vest_asn1 -- --rules ber \
  --der-definition SignedAttributes \
  --der-definition CertificateSet \
  schema.asn1 -o generated_mixed.rs
```

Every ASN.1 definition is emitted exactly once with one global rule. A BER
definition may contain a DER child because a DER encoding is valid BER. A DER
definition cannot depend on a BER definition without violating recursive DER
canonicality. Conflicting transitive overrides are rejected and require an
explicit rule boundary.

DER formats use canonical lengths and applicable primitive encodings. BER
formats accept the supported alternative encodings, including constructed
strings and indefinite containers, then serialize to the backend's normalized
output form. Consequently BER formats do not claim DER-style
non-malleability.

