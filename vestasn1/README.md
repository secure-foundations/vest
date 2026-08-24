# vestasn1

`vestasn1` parses ASN.1 modules with a vendored, locally patched
[`synta-codegen`](https://crates.io/crates/synta-codegen) frontend and emits BER
or DER codecs built directly from `vest_lib2`'s verified ASN.1 primitives and
combinators. DER is the default.

```console
cargo run -- schema.asn1 -o generated.rs
cargo run -- --rules ber schema.asn1 -o generated_ber.rs
```

Individual definitions can use a rule different from the module default. The
selected rule propagates through transitive child references without changing
parent definitions. Each ASN.1 definition has one global rule and is emitted
exactly once:

```console
cargo run -- --rules ber \
  --der-definition SignedAttributes \
  --der-definition CertificateSet \
  schema.asn1 -o generated_mixed.rs
```

A BER definition may contain a DER child because every DER encoding is valid
BER. The reverse would violate recursive DER canonicality, so the compiler
rejects a DER definition that depends on a BER definition. Conflicting
transitive overrides must be resolved with an explicit rule boundary.

## Generated API

Each ASN.1 definition gets a fully verified nominal format type with an
associated `Fmt` value. For example, `AlgorithmIdentifier` becomes the format
type `ALGORITHM_IDENTIFIER`, used as `ALGORITHM_IDENTIFIER::Fmt`.
The nested combinator type is a private implementation detail named `ALGORITHM_IDENTIFIER__`.

`SEQUENCE` and `SET` definitions become named Rust structs, `CHOICE`
definitions become named Rust enums, and `ENUMERATED` definitions become
closed, typed enums. Anonymous composite fields receive deterministic nominal
helper definitions. Verified bidirectional mappers hide Vest's nested tuple and
`Sum`s from users.

The nominal types delegate their specifications and executable operations to
the private combinator formats. `vest_lib2::impl_der!` and
`vest_lib2::impl_ber!` expose the proved parser, serializer, prepare, length,
tagging, and DER-ordering interfaces without re-expanding the nested format at
each use site. This boundary is important for scalable verification of larger
modules such as CMS.

## Supported ASN.1

The backend currently supports:

- BOOLEAN, INTEGER, typed ENUMERATED, OBJECT IDENTIFIER, REAL, NULL, and ANY;
- BIT STRING, OCTET STRING, and the supported character and time strings;
- SEQUENCE, SEQUENCE OF, SET OF, and CHOICE;
- DER heterogeneous SET when its fields are statically in strict canonical tag
  order;
- OPTIONAL and supported DEFAULT components;
- local type references and EXPLICIT/IMPLICIT tags in the context-specific,
  application, and private classes; and
- fixed, bounded, and one-sided SIZE constraints for supported strings and
  collections, plus INTEGER single-value and range constraints.

DER `SET OF` uses the backend's verified DER ordering and rejects unsorted
values during preparation; duplicate encodings remain permitted. BER `SET OF`
does not impose DER ordering. Heterogeneous BER `SET` is not yet generated.

DEFAULT values are supported for BOOLEAN, ENUMERATED, and INTEGER types whose
finite constraint selects the `i8` or `i16` backend required by the current
`Structural + Copy` default representation.

IMPLICIT tagging of CHOICE or ANY is emitted as EXPLICIT because these untagged
formats have no single inherent tag to replace. The generator computes
effective first-tag domains and rejects ambiguous CHOICE and
OPTIONAL/DEFAULT dispatch before verification.

## BER and DER behavior

DER byte strings and applicable character strings borrow from the input. BER
uses owned values where constructed encodings must be flattened, including
`Vec<u8>`, `String` or the relevant owned string representation,
`BitStringOwned`, and `AnyOwned`. Serialization deterministically normalizes
accepted BER alternatives to the backend's selected output form.

BER SEQUENCE uses one schema-shaped field chain ending in `BER_END`; the
specialized backend accepts both definite and indefinite lengths and consumes
EOC only for the indefinite form.

REAL is supported under both rules. `Real<'a, DER>` retains canonical DER
contents. `Real<'a, BER>` additionally accepts BER binary bases, scaling,
non-normalized mantissas, and ISO 6093 NR1/NR2/NR3 decimal forms.

Generated DER nominal formats expose the backend's safety, productivity,
soundness, non-malleability, serialization, unambiguity, and executable
invariants. BER formats expose the applicable safety, productivity,
serialization, unambiguity, and executable invariants, but intentionally do not
claim DER-style soundness or non-malleability.

## Current limitations

Boolean, integer, and ENUMERATED value assignments are emitted as typed Rust
constants inside the generated `verus!` block. OBJECT IDENTIFIER and REAL value
assignments are retained by the frontend but rejected until suitable Verus
constant representations are available.

ENUMERATED executable values currently use the verified `i16` integer-content
backend, so larger numeric members are rejected. BIT STRING SIZE constraints,
RELATIVE-OID, GeneralString, VisibleString, ANY DEFINED BY, and general
constraint combinations are not yet supported. Recursive schema definitions
are rejected until nominal recursive formats are generated with a fixpoint
backend.

Generated disjointness certificates use the ASN.1 identifier's 256 possible
leading octets as a four-word bitmap. Tag numbers 0 through 30 are represented
exactly. All high-tag-number forms (numbers 31 and above) with the same class
and constructed bit share the leading-octet bit for value 31. Therefore the
current proof automation cannot certify two such high tags as disjoint even
when their subsequent base-128 tag-number octets differ; an exact high-tag
fallback is intentionally not implemented yet.

The checked `parse` and `compile` entry points reject extension markers,
extension-addition groups, `WITH COMPONENTS`, imports, and AUTOMATIC TAGS when
the frontend cannot preserve enough information to generate them faithfully. A
recognized but unsupported construct produces a path-aware error instead of a
silent approximation.

## Tests

The checked-in DER, BER, and mixed-rule fixtures under `test/` cover nominal
formats, inline helpers, slice serialization, tagging, OPTIONAL, DEFAULT,
CHOICE, SEQUENCE/SET OF, heterogeneous DER SET, ENUMERATED, OID and REAL round
trips, BER constructed values, SIZE refinements, and generated proof
interfaces.

Run `make test` or `make verify` in `test/` to test or verify the generated
fixtures. Codegen freshness is checked by `cargo test`; set `UPDATE_GOLDEN=1`
when intentionally regenerating the checked-in Rust files.
