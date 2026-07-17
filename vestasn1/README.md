# vestasn1

`vestasn1` parses ASN.1 modules with [`synta-codegen`](https://crates.io/crates/synta-codegen)
and generates DER formats built directly from `vest_lib2`'s verified ASN.1
primitives and combinators.

```console
cargo run -- schema.asn1 -o generated.rs
```

The output is a Rust/Verus module containing one `FooFmt` type and one
notation-style `FOO_FMT()` const function per ASN.1 definition. `SEQUENCE` definitions become named Rust
structs, `CHOICE` definitions become named Rust enums, and `ENUMERATED`
definitions become closed, typed enums. Anonymous composites in fields receive
deterministic helper names. Verified bidirectional mappers hide Vest's internal
nested tuple and `Sum` representations.

The backend supports BOOLEAN, INTEGER, typed ENUMERATED, OBJECT IDENTIFIER,
REAL, ANY, BIT/OCTET STRING, NULL, the Vest-supported character/time strings,
SEQUENCE, SEQUENCE OF, CHOICE, OPTIONAL components, BOOLEAN/ENUMERATED DEFAULT
components, local type references, and explicit/implicit tags. Parsed byte
strings, integers, REAL values, open types, and applicable strings borrow
from the input. Serialization of nominal structures reverse-maps to field
references, avoiding clones and temporary heap allocations.

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
disabled until the backend has an allocation-free DER ordering strategy.
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

The checked-in fixture under `test/` exercises nominal values, inline helpers,
allocation-free slice serialization, tagging, OPTIONAL, DEFAULT, CHOICE,
SEQUENCE OF, ENUMERATED, OID parsing and round trips, REAL, ANY, and a SIZE
refinement. Run `make test` or `make verify` there to regenerate it before
testing or verification.
