# `Bits` Combinator: Current Design and Implementation

This document records the **current** bitfield design in the repository.

It supersedes the older front-end-only plan. The authoritative references are now:

- [`vest_lib2/src/combinators/bits`](../src/combinators/bits)
- [`vest_dev/src/formats/bits.rs`](../../vest_dev/src/formats/bits.rs)

The design center is no longer “bitfields as a hypothetical DSL feature lowered to ad hoc mappers”.
Instead, the core abstraction is a reusable **specification combinator**:

- `Bits<Repr, Tuple, Nominal>` in `vest_lib2`

and the handwritten formats in `vest_dev/src/formats/bits.rs` show the intended generated shape.

## Summary

`Bits` is a **spec/proof-side** combinator for byte-aligned bit-packed formats.

Its job is to package the common structure of bitfield formats:

1. parse one fixed-size carrier integer (`u8`, `u16`, `u24`, `u32`, `u64`)
2. unpack it into a tuple of field values
3. optionally refine that tuple
4. construct the nominal spec value
5. serialize by destructing the nominal value back to a tuple and re-packing it into the carrier

The executable side is still written manually, in the same style as current generated code in
`vest2/test/src/*.rs`.

That split is deliberate:

- spec/proof composition is factored into `vest_lib2`
- exec parsing/serialization/prepare stay explicit and easy to inspect

## Endianness Semantics

The current design supports **byte endianness only**.

That distinction is important:

- the backing representation combinator (`U16Be`, `U16Le`, `U24Be`, `U24Le`, etc.) controls how
  the carrier integer is parsed from / serialized to bytes
- once that carrier integer value exists, bitfield extraction and packing always proceed in
  **DSL field order from most-significant bits to least-significant bits**

There is currently **no independent bit-endianness setting**.

In other words, a definition like:

```text
version_ihl = bits {
    version: u4,
    ihl: u4,
}
```

always means:

- `version` occupies the high 4 bits
- `ihl` occupies the low 4 bits

so its serialized representation is identical regardless of whether the surrounding file uses
`!BIG_ENDIAN` or `!LITTLE_ENDIAN`, because the backing carrier is only one byte.

By contrast, a multi-byte layout such as:

```text
cross_byte_span = bits {
    prefix: u3,
    span: u10,
    suffix: u3,
}
```

uses the same MSB-to-LSB field layout over the 16-bit carrier value in both cases, but the
serialized byte sequence differs because the carrier is written with either `U16Be` or `U16Le`.

This is the intended semantics for the current implementation and the DSL/codegen should document
and test it explicitly.

## Public API

The combinator lives in:

- [`vest_lib2/src/combinators/bits/mod.rs`](../src/combinators/bits/mod.rs)

Its public shape is:

```rust
pub struct Bits<Repr: SpecByteLen, Tuple, Nominal> {
    pub repr: Repr,
    pub unpack: spec_fn(Repr::T) -> Tuple,
    pub pack: spec_fn(Tuple) -> Repr::T,
    pub refinement: PredFnSpec<Tuple>,
    pub ctor: spec_fn(Tuple) -> Nominal,
    pub dtor: spec_fn(Nominal) -> Tuple,
    pub consistent: PredFnSpec<Nominal>,
}
```

This is intentionally closure-based. The generated or handwritten format definition directly names:

- the representation combinator
- the bit unpacking function
- the packing function
- tuple refinement
- constructor / destructor between tuple and nominal spec type
- nominal consistency predicate

### Representative usage

From `vest_dev/src/formats/bits.rs`, the intended spec-level shape is:

```rust
pub type PacketHeaderFmtSpec = Named<Bits<U16Be, (u8, u8, u8), PacketHeaderSpec>>;

impl PacketHeaderFmt {
    pub open spec fn spec_inner() -> PacketHeaderFmtSpec {
        Named(
            "packet_header",
            Bits {
                repr: U16Be,
                unpack: |packed: u16| unpack_packet_header(packed),
                pack: |unpacked: (u8, u8, u8)| {
                    let (kind_bits, count, len) = unpacked;
                    pack_packet_header(kind_bits, count, len)
                },
                refinement: |unpacked: (u8, u8, u8)| -> bool {
                    let (_kind_bits, count, _len) = unpacked;
                    count >= 1u8
                },
                ctor: |unpacked: (u8, u8, u8)| -> PacketHeaderSpec {
                    let (kind_bits, count, len) = unpacked;
                    let kind = payload_kind_from_bits(kind_bits);
                    PacketHeaderSpec { kind, count, len }
                },
                dtor: |value: PacketHeaderSpec| -> (u8, u8, u8) {
                    let PacketHeaderSpec { kind, count, len } = value;
                    let kind_bits = payload_kind_to_bits(kind);
                    (kind_bits, count, len)
                },
                consistent: |value: PacketHeaderSpec| -> bool {
                    let PacketHeaderSpec { kind, count, len } = value;
                    &&& payload_kind_wf(kind)
                    &&& packet_header_bounds(payload_kind_to_bits(kind), count, len)
                },
            },
        )
    }
}
```

This is the template the DSL/codegen should target.

## Internal Desugaring

The helper function in
[`vest_lib2/src/combinators/bits/spec.rs`](../src/combinators/bits/spec.rs)
shows the exact internal meaning:

```rust
pub open spec fn bits<Repr: SpecByteLen, Tuple, Nominal>(
    repr: Repr,
    unpack: spec_fn(Repr::T) -> Tuple,
    pack: spec_fn(Tuple) -> Repr::T,
    refinement: PredFnSpec<Tuple>,
    ctor: spec_fn(Tuple) -> Nominal,
    dtor: spec_fn(Nominal) -> Tuple,
) -> Mapped<
    Refined<Mapped<Repr, BiMapper<Repr::T, Tuple>>, PredFnSpec<Tuple>>,
    BiMapper<Tuple, Nominal>,
>
```

So `Bits` is not magic. It is a named, direct surface over the recurring pattern:

1. `Mapped<Repr, BiMap(unpack, pack)>`
2. `Refined(..., refinement)`
3. `Mapped(..., BiMap(ctor, dtor))`

The additional `consistent` field is **not** part of this internal desugaring. It is added by
`Bits` itself at the outer `Consistency` / `SoundParser` / `SPRoundTripDps` layer.

That is the key difference between `Bits` and merely spelling the nested `Mapped/Refined/Mapped`
stack directly.

## Spec Semantics

Implemented in:

- [`vest_lib2/src/combinators/bits/spec.rs`](../src/combinators/bits/spec.rs)

### Parsing

`Bits::spec_parse` delegates to the internal desugared format:

1. parse `repr`
2. unpack the carrier into the tuple
3. require `refinement(tuple)`
4. return `ctor(tuple)`

So parse acceptance is controlled by:

- `repr`
- `refinement`

and **not** directly by the outer `consistent` predicate.

This is important for open/closed enum cases:

- open enums may parse more raw encodings and normalize them to `Unknown(x)`
- closed enums use the tuple refinement to reject invalid raw encodings at parse time

### Serialization

Serialization is:

1. `dtor(nominal)`
2. `pack(tuple)`
3. serialize with `repr`

### Consistency

`Bits::consistent` is stronger than the internal `Mapped/Refined/Mapped` consistency:

```rust
let fmt = bits(...);
&&& fmt.consistent(v)
&&& self.consistent(v)
```

In other words, a nominal value is consistent only if:

1. destructing it yields a tuple accepted by the tuple refinement
2. re-packing that tuple is consistent with the representation combinator
3. the nominal-specific semantic predicate holds

This split is intentional:

- `refinement` talks about the unpacked tuple and affects parsing
- `consistent` talks about the nominal value and affects serializer/prepare admissibility

## Proof Structure

Implemented in:

- [`vest_lib2/src/combinators/bits/proof.rs`](../src/combinators/bits/proof.rs)

The proof story is deliberately lightweight:

- reuse the internal `bits(...)` desugaring where possible
- expose only the extra obligations that are specific to the `Bits` abstraction

### `SoundParser`

`Bits::sound_inv()` currently requires:

1. the internal `bits(...)` format is sound
2. every value returned by the internal parse path satisfies the outer nominal `consistent`

Concretely:

```rust
&&& fmt.sound_inv()
&&& forall|ibuf| #[trigger]
    fmt.spec_parse(ibuf) matches Some((_, v)) ==> (self.consistent)(v)
```

This means the format-specific wrapper must prove that its constructor normalizes parsed tuples
into semantically well-formed nominal values.

For simple layouts like `version_ihl` and `cross_byte_span`, this reduces to showing:

- `unpack(raw)` always satisfies the field-width bounds

For enum-bearing layouts like `packet_header`, this additionally requires:

- `payload_kind_from_bits(kind_bits)` is well-formed under the parsed bit-width bound

### `SPRoundTripDps`

`Bits::unambiguous()` is where the tuple/nominal isomorphism obligations surface.

The current shape is:

```rust
&&& self.repr.unambiguous()
&&& forall|unpacked: Tuple|
    (#[trigger] (self.consistent)((self.ctor)(unpacked)) && (self.refinement)(unpacked))
        ==> (self.unpack)((self.pack)(unpacked)) == unpacked
&&& forall|t: Nominal| #[trigger]
    (self.consistent)(t) ==> (self.ctor)((self.dtor)(t)) == t
```

So to use `Bits` as a roundtrip-capable leaf-ish format, each concrete wrapper must prove:

1. `unpack(pack(tuple)) == tuple` on refined consistent tuples
2. `ctor(dtor(value)) == value` on consistent nominal values

This is why `vest_dev/src/formats/bits.rs` still contains manual proof glue around
`fmt.1.unambiguous()`.

### `NonMalleable`, `NoLookAhead`, `Productive`, `EquivSerializers`

These mostly delegate to the internal desugaring.

The critical format-specific work remains:

- proving the `SoundParser` precondition
- proving the `SPRoundTripDps::unambiguous()` precondition

Once those are in place, the rest of the traits tend to follow the same pattern as other
named leaf formats.

## Authoritative Reference Patterns

The file
[`vest_dev/src/formats/bits.rs`](../../vest_dev/src/formats/bits.rs)
is the current reference for how bitfield formats should be written/generated.

The important cases are:

### 1. `VersionIhl`

Smallest useful case:

- carrier: `U8`
- tuple: `(u8, u8)`
- no parse-time refinement beyond representable widths (`refinement: true`)
- nominal consistency: `version_ihl_bounds(...)`

This is the simplest template for:

- a byte-sized packed record
- field-width constraints carried only in `consistent`

### 2. `CrossByteSpan`

Cross-byte field slicing over `U16Be`:

- carrier: `U16Be`
- tuple: `(u8, u16, u8)`
- again `refinement: true`
- nominal consistency captures representable widths

This is the template for multi-field packed layouts that span byte boundaries but still have no
semantic cross-field dependency.

### 3. `PacketHeader`

Open enum case:

- carrier: `U16Be`
- tuple: `(kind_bits, count, len)`
- parse-time tuple refinement: `count >= 1`
- constructor maps `kind_bits` into an open enum with `Unknown(x)`
- nominal consistency adds:
  - `payload_kind_wf(kind)`
  - field-width bounds through `packet_header_bounds(...)`

This demonstrates the intended split:

- raw parse filtering is done by `refinement`
- semantic enum well-formedness is done by the nominal `consistent`

### 4. `ClosedPacketHeader`

Closed enum case:

- same packed representation as `PacketHeader`
- stronger tuple refinement:
  - `kind_bits < 3`
  - `count >= 1`
- constructor maps into a closed enum

This is the template for exhaustive enums embedded inside bitfields.

## Open and Closed Bit-Sized Enums

The authoritative examples are in:

- `payload_kind`
- `closed_payload_kind`

from [`vest_dev/src/formats/bits.rs`](../../vest_dev/src/formats/bits.rs).

These two cases drive the codegen strategy for enum-backed bitfields.

### Open bit-sized enums

Open enums use the existing Vest “unknown/default” story:

- known bit patterns map to named variants
- all remaining in-range bit patterns map to `Unknown(x)`

In the handwritten reference:

```rust
pub enum PayloadKind {
    Raw = 0,
    Words = 1,
    Tiny = 2,
    Unknown(u8),
}
```

with helpers:

```rust
payload_kind_from_bits(bits: u8) -> PayloadKind
payload_kind_to_bits(kind: PayloadKind) -> u8
payload_kind_wf(kind: PayloadKind) -> bool
```

Codegen strategy:

1. generate the exec/spec enum with an `Unknown(carrier)` variant
2. generate `from_bits`, `to_bits`, and `wf` helpers
3. keep parse-time tuple refinement focused only on raw structural constraints
   - e.g. `count >= 1`
4. put enum well-formedness into the nominal `consistent` closure of `Bits`

That gives the intended semantics:

- parsing accepts any in-range bit pattern for the enum field
- serialization only accepts semantically well-formed open-enum values

For `packet_header`, that is exactly:

```rust
consistent: |value: PacketHeaderSpec| -> bool {
    let PacketHeaderSpec { kind, count, len } = value;
    &&& payload_kind_wf(kind)
    &&& packet_header_bounds(payload_kind_to_bits(kind), count, len)
}
```

### Closed bit-sized enums

Closed enums do not have an unknown/default variant. In the handwritten reference:

```rust
pub enum ClosedPayloadKind {
    Raw = 0,
    Words = 1,
    Tiny = 2,
}
```

The key difference is that invalid raw bit patterns are rejected at parse time.

Codegen strategy:

1. generate the closed enum datatype
2. generate `from_bits` and `to_bits`
3. encode enum admissibility as part of the tuple refinement
   - e.g. `kind_bits < 3`
4. keep the nominal `consistent` predicate focused on the serialized tuple bounds

For `closed_packet_header`, that is:

```rust
refinement: |unpacked: (u8, u8, u8)| -> bool {
    let (kind_bits, count, _len) = unpacked;
    &&& kind_bits < 3u8
    &&& count >= 1u8
},
```

and:

```rust
consistent: |value: ClosedPacketHeaderSpec| -> bool {
    let ClosedPacketHeaderSpec { kind, count, len } = value;
    packet_header_bounds(closed_payload_kind_to_bits(kind), count, len)
}
```

This gives the intended semantics:

- parse rejects non-enum raw encodings immediately
- serialize only needs to reason about valid closed-enum values

### Summary of enum codegen policy

For bit-sized enums inside `bits { ... }`:

- **open enum**:
  - generate `Unknown(...)`
  - do not refine away unknown bit patterns
  - enforce enum semantic well-formedness in nominal `consistent`

- **closed enum**:
  - no `Unknown(...)`
  - refine away invalid bit patterns at parse time
  - nominal `consistent` does not need a separate enum-wf clause

This distinction should be treated as part of the stable backend shape for DSL codegen.

## Pack/Unpack Helpers and Lemmas

The current recommended helper pattern is the one used in `bits.rs`.

For each layout, define:

1. `unpack_*`
2. `pack_*`
3. `*_bounds`
4. bitvector lemmas:
   - `lemma_*_unpack_pack`
   - `lemma_*_pack_unpack`
   - `lemma_*_mapper_wf_in_out`

Example:

```rust
#[verifier::allow_in_spec]
pub fn unpack_version_ihl(raw: u8) -> (u8, u8) { ... }

#[verifier::allow_in_spec]
pub fn pack_version_ihl(version: u8, ihl: u8) -> u8 { ... }

#[verifier::allow_in_spec]
pub fn version_ihl_bounds(version: u8, ihl: u8) -> bool { ... }

pub broadcast proof fn lemma_version_ihl_unpack_pack(raw: u8)
    by (bit_vector)
    ensures
        #[trigger] pack_version_ihl(unpack_version_ihl(raw).0, unpack_version_ihl(raw).1) == raw,
{ }
```

The key point is that the bitvector solver can usually discharge the layout-level arithmetic
completely automatically, as long as the helper functions are stated in this flattened style.

The remaining proof burden is normally not bit arithmetic. It is the semantic glue:

- tuple refinement
- open vs closed enum reconstruction
- nominal consistency

## Standard Derived-Proof Pattern

In the wrapper proof section for `bits { ... }` formats, there is now a standard local proof
pattern. The `version_ihl` wrapper in
[`vest_dev/src/formats/bits.rs`](../../vest_dev/src/formats/bits.rs)
is the reference.

The three broadcast lemmas generated from the pack/unpack helpers are used in a fixed way:

### For `SoundParser` and `NonMalleable`

Use:

```rust
broadcast use lemma_version_ihl_unpack_pack, lemma_version_ihl_mapper_wf_in_out;
```

This is the standard pair for:

- `SoundParser::lemma_parse_sound_consumption`
- `SoundParser::lemma_parse_sound_value`
- `NonMalleable::lemma_parse_non_malleable`

Semantically:

- `lemma_*_unpack_pack` provides the lossless raw-layout roundtrip
- `lemma_*_mapper_wf_in_out` provides the tuple bounds / raw-layout well-formedness fact

### For `SPRoundTripDps`

Use:

```rust
broadcast use lemma_version_ihl_pack_unpack;
```

This is the standard broadcast lemma for:

- `SPRoundTripDps::theorem_serialize_dps_parse_roundtrip`

Semantically, it discharges the `Bits::unambiguous()` side condition that requires:

- `unpack(pack(tuple)) == tuple`

on refined consistent tuples.

### Codegen implication

This broadcast-lemma pattern should be treated as part of the generated proof shape for bitfield
formats:

1. generate the three broadcast proofs:
   - `lemma_*_unpack_pack`
   - `lemma_*_pack_unpack`
   - `lemma_*_mapper_wf_in_out`
2. use:
   - `unpack_pack + mapper_wf_in_out` in `SoundParser` and `NonMalleable`
   - `pack_unpack` in `SPRoundTripDps`

This is now part of the intended backend contract for bitfield codegen, not just an incidental
proof trick in the handwritten examples.

## Exec Side: Still Manual

`Bits` is currently **not** an exec combinator.

The executable `Parser` / `Serializer` / `Prepare` impls in `vest_dev/src/formats/bits.rs`
remain manual and follow the generated-code style:

- parse the carrier integer with `U8`, `U16Be`, etc.
- unpack it using `unpack_*`
- perform explicit runtime checks for tuple refinement
- build the nominal exec value

and symmetrically for serialize / prepare:

- destruct the nominal value
- pack the tuple
- delegate to the carrier integer combinator

This is the current intended split for DSL/codegen as well:

- spec side: emit `Bits { ... }`
- exec side: emit direct code

## Codegen Target Shape

The current codegen target implied by this design is:

### Spec side

Generate:

1. carrier choice (`U8`, `U16Be`, `U24Le`, `U32Be`, `U64Le`, etc.)
2. `unpack_*` / `pack_*` / `*_bounds`
3. broadcast bitvector lemmas
4. `spec_inner()` returning:

```rust
Named(
    "format_name",
    Bits {
        repr: ...,
        unpack: ...,
        pack: ...,
        refinement: ...,
        ctor: ...,
        dtor: ...,
        consistent: ...,
    },
)
```

5. wrapper proof impls in the style currently used in `bits.rs`

### Exec side

Generate manual:

- `impl Parser`
- `impl Serializer`
- `impl Prepare`

for the nominal exec datatype, using the pack/unpack helpers directly.

## Relationship to the DSL Design

The older document treated bitfields mainly as a DSL-front-end feature.

The current implementation suggests a sharper split:

1. the DSL should still expose a `bits { ... }` surface
2. but the core backend target should be this `Bits` combinator plus manual exec code

That means the front-end design should now be understood as:

- parse a `bits { ... }` block in `vest2`
- elaborate/typecheck it into:
  - one representation carrier
  - one tuple layout
  - one nominal generated datatype
  - one generated `Bits { ... }` spec definition
  - one set of pack/unpack/bounds/bitvector lemmas
  - one set of manual exec impls

This is materially different from the older “just lower to `Mapped<...>` directly” story.
`Bits` is now the intended public spec-side backend primitive.

## Current Limitations

This document reflects the current implemented direction, not an idealized finished feature.

Notable current limitations:

1. `Bits` is spec/proof-side only
2. wrapper proof impls still need manual format-specific glue
3. the tuple/nominal roundtrip obligations are still exposed at the wrapper layer
4. `vest_dev/src/formats/bits.rs` remains the primary reference for those local proof shapes

These are acceptable for now because they keep:

- the semantics clear
- the generated exec code explicit
- the bitvector-heavy reasoning local and automatable

## Practical Guidance

When adding a new bitfield format today:

1. choose a byte-aligned integer representation combinator
2. write `unpack_*`, `pack_*`, and `*_bounds`
3. prove the three bitvector lemmas as broadcast proofs
4. define `spec_inner()` using `Bits`
5. add manual wrapper proofs following `version_ihl` / `cross_byte_span` / `packet_header`
6. write explicit exec `parse` / `serialize` / `prepare`

If in doubt, treat `vest_dev/src/formats/bits.rs` as the source of truth. This document is meant
to explain that file, not replace it.
