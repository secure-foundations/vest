# Bit-Packed Ints in Vest v1

## Summary

This document records the recommended v1 design for bit-packed integers in the Vest DSL in
`vest2/src`.

The chosen direction is:

- add an explicit `bits { ... }` block to the DSL
- keep v1 unsigned-only for non-byte-aligned integers
- keep bit endianness separate from the existing byte endianness
- require each `bits` block to be byte-aligned and to fit into exactly one existing fixed-size
  byte-aligned integer carrier: `u8`, `u16`, `u24`, `u32`, or `u64`
- keep the emitted Rust values as ordinary Rust integer carrier types and ordinary generated
  structs/enums
- keep the exec side manual, following the current generated style, rather than relying on
  `Mapped` exec implementations

This design is intentionally conservative. It preserves the current byte-oriented parser and
serializer traits in `vest_lib2`, while still making bit-packed integers first-class values in the
DSL for:

- refinements
- field access
- dependent choices
- dependent byte arrays
- dependent `RepeatN`
- dependent `AndThen` / `[u8; @l] >>= fmt`

It does **not** attempt full bit-stream parsing in v1. Mid-byte transitions between arbitrary
combinators remain out of scope.

---

## DSL Surface

### `bits { ... }`

Introduce a new combinator form:

```vest
!BIG_ENDIAN
!BIT_BIG_ENDIAN

ipv4_prelude = bits {
    version: u4 | 4,
    ihl: u4 | { 5..15 },
    dscp: u6,
    ecn: u2,
    @total_len: u16 | { 20..0xffff },
}
```

Semantics:

- a `bits` block is a flat sequence of integer-like fields
- fields inside the block are interpreted in bit order
- the entire block is parsed and serialized as one fixed-size integer carrier
- once the block finishes, parsing resumes at the next byte boundary

### Bit endianness

Bit endianness must be a distinct DSL control. Reusing the current `!LITTLE_ENDIAN` /
`!BIG_ENDIAN` for both byte order and bit order would make the semantics too implicit.

Recommended v1 surface:

```vest
!LITTLE_ENDIAN
!BIT_BIG_ENDIAN
```

or

```vest
!BIG_ENDIAN
!BIT_LITTLE_ENDIAN
```

For v1 this should be file-global only.

### Bit-sized integers

Inside `bits { ... }`, permit arbitrary unsigned widths:

- `u1`
- `u3`
- `u7`
- `u10`
- `u18`
- ...
- `u64`

Outside `bits { ... }`, keep the current restriction:

- only byte-oriented integer widths currently supported by Vest

### Bit-sized enums

Do not add a new enum syntax. Extend the existing type-suffixed literal story instead.

Today byte-sized enums use examples like:

```vest
a_typed_open_enum = enum {
  P = 0x00u32,
  Q = 0x01u32,
  R = 0x02u32,
  ...
}
```

Bit-sized enums should use the same idea, with the suffix grammar extended to the new widths:

```vest
payload_kind = enum {
  Raw   = 0u3,
  Words = 1,
  Tiny  = 2u3,
  ...
}
```

Notes:

- all explicitly suffixed literals in one enum must still agree
- the enum’s declared or inferred underlying width must fit in the surrounding bitfield width
- plain `enum { ... }` should keep its current byte-oriented inference behavior

---

## v1 Restrictions

### Whole-block representation

For v1, each `bits` block must satisfy both:

1. total width is a multiple of 8
2. total width is exactly one of:
   - `8`
   - `16`
   - `24`
   - `32`
   - `64`

This is the main additional restriction relative to the broader Route A discussion.

So the spec-side carrier is always one existing fixed-size int combinator, for example:

```rust
Named<Mapped<U32Be, Ipv4PreludeMapper>>
```

instead of:

```rust
Named<Mapped<Fixed<4>, Ipv4PreludeMapper>>
```

If the block also has DSL-level refinements, those may still appear as an outer `Refined(...)`
around the mapped block or around the underlying carrier, depending on codegen convenience.

### Allowed contents inside `bits`

Keep v1 intentionally narrow. Inside a `bits` block, allow only:

- unsigned integer fields `u1..u64`
- constrained integer fields
- enum fields whose underlying integer width is valid in the block
- const integer and const enum fields

Disallow in v1:

- nested ordinary structs
- nested `bits` blocks
- `Vec`
- `Option`
- `Tail`
- `Bytes`
- `Array`
- `Wrap`
- `>>=`

This restriction is only for the interior of the block. Once the block has been parsed into
ordinary values, those values can drive all the existing dependent combinators outside.

---

## Value Model and Emitted Rust API

### Carrier types

Bit-sized integer fields should be emitted as ordinary Rust integer carrier types:

- widths `1..=8` map to `u8`
- widths `9..=16` map to `u16`
- widths `17..=32` map to `u32`
- widths `33..=64` map to `u64`

This is the same compatibility story Vest already uses for `u24`, which is represented as `u32`.

Examples:

- `u1`, `u3`, `u7` -> `u8`
- `u10` -> `u16`
- `u18` -> `u32`

### Consistency

The width invariant belongs to the format, not to the runtime datatype.

For example, for a field `version: u3`, the emitted Rust field is still `u8`, but consistency
requires:

```rust
version <= 0x7u8
```

The same pattern applies to open enums and closed enums:

- open enum unknown values must still fit within the field width
- closed enums must reject values not represented by the enum

This keeps emitted Rust values compatible with the current generated style in `vest2/test/src`.

### Field access and dependency

Once parsed, bitfield values are ordinary typed values. That means existing dependent forms should
keep working without new surface syntax:

```vest
packet = {
    @hdr: bits {
        @kind: payload_kind,
        @count: u5,
        @len: u8,
    },
    body: [u8; @hdr.len] >>= choose(@hdr.kind) {
        Raw => [u8; @hdr.len],
        Words => [u16; @hdr.count],
        _ => Tail,
    },
}
```

This is one of the main reasons to make bitfields produce ordinary ints and ordinary generated
structs rather than introducing dedicated runtime bitfield wrapper types.

---

## Frontend Changes in `vest2/src`

### Grammar / AST

Add:

- a `bits` combinator node
- parsing support for arbitrary unsigned widths in integer type syntax
- typed integer suffix parsing for non-byte widths in enum literals
- a file-global bit-endianness directive

Suggested grammar extensions:

- `bit_struct_combinator = { "bits" ~ "{" ~ ... ~ "}" }`
- widen integer width parsing from the current fixed set to a decimal width token that is later
  validated by context
- extend typed integer literal suffixes from the current byte-oriented widths to `u1..u64`

### Elaboration

Keep elaboration simple:

- anonymous `bits { ... }` blocks should be lifted the same way anonymous inline combinators are
  lifted today
- no implicit grouping of adjacent bit-sized fields in ordinary structs

### Type checking

Type checking needs to enforce:

1. non-byte widths are only legal inside `bits { ... }`
2. the block total width is one of `8/16/24/32/64`
3. every enum / const / refinement fits its declared width
4. dependent use sites such as `[u8; @l]`, `[fmt; @l]`, `choose(@x)`, and `[u8; @l] >>= fmt`
   accept bitfield-derived integer values the same way they accept existing integer values

The existing typed `LengthExpr` pipeline in `vestir` should be reused. The main change is that
integer width legality and width-to-carrier mapping become broader in bitfield contexts.

---

## Library Support in `vest_lib2`

### Placement

The small reusable helper layer for bit operations should live under:

- `vest_lib2/src/combinators/uints`

as a new file / submodule, alongside the existing byte-aligned integer support.

This helper layer should include:

- spec-level bit extraction helpers
- spec-level bit insertion helpers
- proof lemmas for roundtrip and range facts
- exec helper functions with `ensures` linking them back to the spec-level helpers

Suggested responsibilities:

```rust
pub open spec fn extract_bits_be_u64(value: u64, start: nat, width: nat) -> u64;
pub open spec fn insert_bits_be_u64(base: u64, start: nat, width: nat, field: u64) -> u64;

pub open spec fn extract_bits_le_u64(value: u64, start: nat, width: nat) -> u64;
pub open spec fn insert_bits_le_u64(base: u64, start: nat, width: nat, field: u64) -> u64;
```

and exec counterparts specialized to the supported carriers:

```rust
pub fn extract_bits_be_u16(value: u16, start: usize, width: usize) -> (out: u16)
    ensures out as u64 == extract_bits_be_u64(value as u64, start as nat, width as nat);
```

The helper layer should be proof-oriented infrastructure only. It should **not** introduce a new
bit-aware parser trait family in v1.

### Exec side

For the exec side of bitfield formats, do **not** rely on `Mapped` exec implementations.

Instead, follow the current generated style used in `vest2/test/src`:

- parse the underlying carrier using an existing exec int combinator like `U16Be`
- extract fields explicitly in the generated parser body
- pack fields explicitly in the generated serializer body
- compute `prepare()` directly, with explicit compliance checks

This keeps the generated exec code aligned with the rest of the codegen strategy and avoids
needing new exec trait coverage for `Mapped`.

---

## Codegen Shape

### Spec side

For a bitfield block with no extra DSL-level refinement:

```rust
pub type PacketHeaderFmtSpec = Named<Mapped<U16Be, PacketHeaderMapper>>;
```

If the block has additional refinement not guaranteed by the raw width partitioning, wrap that
using the existing refinement pattern:

```rust
pub type PacketHeaderFmtSpec =
    Named<Refined<Mapped<U16Be, PacketHeaderMapper>, PredFnSpec<PacketHeaderSpec>>>;
```

The mapper is responsible for:

- unpacking the carrier into a generated spec struct
- packing the struct back into the carrier
- declaring `wf_out` for width / enum-shape constraints
- proving `LossyMapper` / `LosslessMapper`

### Exec side

The generated exec wrapper should look like the current generated code:

```rust
impl Parser<&[u8]> for PacketHeaderFmt {
    type PT = PacketHeader;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        reveal(<PacketHeaderFmt as SpecParser>::spec_parse);
        let (n, raw) = U16Be.parse(ibuf)?;
        let value = unpack_packet_header(raw);
        if !(value.count >= 1) {
            return Err(ParseError::predicate_failed());
        }
        assert(self.spec_parse(ibuf@) == Some((n as int, value.deep_view())));
        Ok((n, value))
    }
}
```

Serializer and `Prepare` should mirror that style:

- `serialize()` packs to the carrier then delegates to the existing integer combinator
- `prepare()` checks compliance and returns the carrier byte length

---

## Experimental Reference Implementation

Before touching the generator, the intended shape should be prototyped manually in
`vest_dev/src/formats`.

The prototype should cover:

1. **Basic packing**
   - one byte-wide packed struct, e.g. `u4 + u4`
2. **Cross-byte fields**
   - e.g. `u3 + u10 + u3` in a `U16Be` carrier
3. **Refinements**
   - field-level refinement not guaranteed by width alone
4. **Bit-sized enums**
   - using the ordinary typed-literal idea, not a second enum syntax
5. **Dependency into bytes**
   - a later `[u8; @hdr.len]`
6. **Dependency into `RepeatN`**
   - a later `[u16; @hdr.count]`
7. **Dependency into `choose`**
   - a dependent payload chosen from a bitfield-derived enum

The handwritten module should mirror the current generated style in `vest2/test/src`:

- public runtime datatypes and spec datatypes
- mapper types
- named format wrappers with `spec_inner()`
- proof trait impls by delegation to the underlying spec combinators
- explicit exec `Parser` / `Serializer` / `Prepare` impls

The first experiment should remain in `vest_dev/src/formats` even if some helpers are duplicated
locally. The point is to validate the generated-code shape before baking support into `vest2`
codegen and `vest_lib2`.

---

## Out of Scope for v1

These should be explicitly deferred:

- signed non-byte widths (`i1`, `i3`, `i10`, ...)
- arbitrary mid-byte transitions between unrelated combinators
- nested `bits` blocks
- implicit auto-grouping of adjacent bit-sized fields
- a new bit-aware parser / serializer trait family in `vest_lib2`

If the project later needs fully general bit-stream parsing, that should be treated as a separate
library architecture change rather than an incremental extension of this v1 design.
