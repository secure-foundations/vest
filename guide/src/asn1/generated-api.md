# ASN.1 generated API

An ASN.1 definition such as `AlgorithmIdentifier` becomes a Rust value type and
a fully verified nominal format type such as `ALGORITHM_IDENTIFIER`, used as
`ALGORITHM_IDENTIFIER::Fmt`.

`SEQUENCE` and supported heterogeneous `SET` definitions become structs;
`CHOICE` becomes an enum; and `ENUMERATED` becomes a closed typed enum.
Anonymous composites receive deterministic private helper definitions.
Bidirectional mappers hide nested tuple and `Sum` representations.

The nominal format exposes parsing, preparation, byte length, in-place
serialization, retagging, and the proof traits valid under its encoding rule.
DER formats also compose through the allocation-free ordering interface needed
by DER `SET OF`.

DER byte and character strings borrow from the input where possible. BER uses
owned values when constructed encodings must be flattened. This difference is
visible in generated Rust types and may require the `alloc` feature.

IMPLICIT tagging replaces the outer tag. Untagged `CHOICE` and `ANY` have no
single tag to replace, so the generator uses explicit tagging for those cases.

