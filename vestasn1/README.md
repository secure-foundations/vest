# vestasn1

`vestasn1` parses ASN.1 modules with [`synta-codegen`](https://crates.io/crates/synta-codegen)
and generates BER or DER formats built directly from `vest_lib2`'s verified
ASN.1 primitives and combinators. DER remains the default.

```console
cargo run -- schema.asn1 -o generated.rs
cargo run -- --rules ber schema.asn1 -o generated_ber.rs
```

The output is a Rust/Verus module containing one `FooFmt` type and one
notation-style `FOO_FMT()` const function per ASN.1 definition. `SEQUENCE` definitions become named Rust
structs, `CHOICE` definitions become named Rust enums, and `ENUMERATED`
definitions become closed, typed enums. Anonymous composites in fields receive
deterministic helper names. Verified bidirectional mappers hide Vest's internal
nested tuple and `Sum` representations.

The backend supports BOOLEAN, INTEGER, typed ENUMERATED, OBJECT IDENTIFIER,
ANY, BIT/OCTET STRING, NULL, the Vest-supported character/time strings,
SEQUENCE, SEQUENCE OF, CHOICE, OPTIONAL components, BOOLEAN/ENUMERATED DEFAULT
components, local type references, and explicit/implicit tags. Parsed byte
strings and applicable strings borrow from the input under DER. BER uses owned
values where constructed encodings must be flattened: `Vec<u8>`, owned string
wrappers, `BitStringOwned`, and `AnyOwned`. BER serializers deterministically
normalize these values to primitive or definite-length encodings.

Generated DER modules prove parser safety, soundness, and the library's
destination-passing unambiguity invariant. Generated BER modules prove safety
and unambiguity, but deliberately do not claim DER-style parser soundness.
For BER `SEQUENCE`, the generator emits a definite body ending in the real
`Eof` combinator and an indefinite body ending in the EOC-consuming
`EOC_END`; both have the same semantic tuple. This keeps terminal
`OPTIONAL`/`DEFAULT` fields compositional.

REAL is supported under both rules. The zero-copy `Real<'a, DER>` value retains
canonical DER contents; `Real<'a, BER>` additionally accepts BER binary
bases/scaling/non-normalized mantissas and ISO 6093 NR1/NR2/NR3 decimal forms.

IMPLICIT tags applied to CHOICE or ANY are promoted to EXPLICIT as required by
their lack of a replaceable inherent tag. The generator analyzes effective tag
domains and rejects ambiguous CHOICE and OPTIONAL/DEFAULT dispatch before
verification. Fixed, bounded, and one-sided string and `SEQUENCE OF SIZE`
constraints are emitted with the backend's verified `Size` predicate. INTEGER
single-value and range constraints use the verified `IntegerRange` predicate.

Boolean, integer, and ENUMERATED value assignments are emitted as typed Rust
constants inside the generated `verus!` block. OBJECT IDENTIFIER value
assignments are retained by the vendored Synta frontend but rejected by codegen
until the backend has a suitable Verus const representation.

`SET` and `SET OF` are currently rejected. Generic `SET OF` generation remains
disabled until rule-correct ordering and duplicate handling are implemented.
Generated ENUMERATED executable values currently use the verified `i16`
integer-content backend, so larger numeric members are rejected explicitly.
A schema construct whose constraints or encoding semantics are not implemented
is rejected with a path-aware error rather than silently approximated.

The checked `parse`/`compile` entry points reject extension markers, extension
addition groups, and `WITH COMPONENTS`. Synta 0.3.0 removes those constructs
from its public AST, so accepting them would otherwise silently change the
schema. The patched parser also preserves `SEQUENCE/SET SIZE ... OF`, local
typed value assignments, named scalar values, and OID references directly in
its AST. `SEQUENCE OF` is generated and `SET OF` remains rejected for the
DER-ordering reason above.

The checked-in DER and BER fixtures under `test/` exercise nominal values, inline helpers,
allocation-free slice serialization, tagging, OPTIONAL, DEFAULT, CHOICE,
SEQUENCE OF, ENUMERATED, OID parsing and round trips, REAL, recursive
indefinite-length ANY, constructed OCTET/BIT/character strings, and SIZE
refinements. Run `make test` or `make verify` there to regenerate them before
testing or verification.
