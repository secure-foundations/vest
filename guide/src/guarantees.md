# What Vest proves

Vest separates a format into three related layers:

1. pure specifications for parsing, serialization, byte length, and value
   consistency;
2. executable Rust implementations; and
3. proofs connecting the implementations to the specifications and composing
   format-level properties.

Verus checks executable memory safety, panic freedom, termination, and the
contracts on the parsing, preparation, length, and serialization APIs. The
following properties describe the wire format itself.

| Property | Vest interface | Meaning |
|---|---|---|
| Safe parsing | `SafeParser` | A successful specification parse consumes a valid prefix of the input. |
| Parser soundness | `SoundParser` | The parsed value is consistent and the consumed length agrees with its specified byte length. |
| Serialize–parse round trip | `SPRoundTripDps` / `SPRoundTrip` | Serializing a consistent value and parsing the result recovers that value. |
| Parser non-malleability | `NonMalleable` | Equal parsed values imply equal consumed bytes. |
| Parse–serialize round trip | `PSRoundTrip` | Serializing a successful parse reproduces exactly the consumed input prefix. |
| No lookahead | `NoLookAhead` | Parsing a prefix does not depend on bytes after the consumed region. |
| Productivity | `Productive` | A successful parse consumes at least one byte when its productivity invariant holds. |
| Serializer equivalence | `EquivSerializers` | The ordinary and destination-passing specifications agree. |

Serialize–parse round trip also implies that serialization is injective over
consistent values. Parse–serialize round trip follows compositionally from
serialize–parse round trip, parser soundness, and non-malleability.

Not every legal wire format is non-malleable. BER, general CBOR, ordered
alternatives, and permutation formats deliberately accept multiple byte
representations in some configurations. Such formats expose the properties
that genuinely hold rather than claiming canonicality. DER formats and
deterministic encodings can establish stronger properties when their format
rules remove those alternatives.

The exact quantified statements and invariant preconditions are in the
[`core::proof`](https://secure-foundations.github.io/vest/vest_lib/core/proof/)
and
[`core::spec`](https://secure-foundations.github.io/vest/vest_lib/core/spec/)
API documentation.

