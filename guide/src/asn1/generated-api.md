# Generated Rust Code

An ASN.1 definition such as `Packet` becomes a Rust value type `Packet` and a
verified nominal format type `PACKET`, used as `PACKET::Fmt`. The screaming-case
format name avoids colliding with the idiomatic value name.

`SEQUENCE` and supported heterogeneous `SET` definitions become structs;
`CHOICE` becomes an enum carrying the alternatives; and `ENUMERATED` becomes a
closed typed enum. Anonymous composites receive deterministic private helper
definitions. `IMPLICIT` tagging replaces the outer tag; untagged `CHOICE` and
`ANY` have no single tag to replace, so the generator tags those explicitly.

The examples below come from the module in the [tutorial](tutorial.md):

```asn1
Kind   ::= ENUMERATED { request(0), response(1) }
Packet ::= SEQUENCE {
    kind    Kind,
    payload [0] IMPLICIT OCTET STRING (SIZE (1..32)) OPTIONAL
}
```

## The shape of an emitted file

Unlike a DSL-generated module, an ASN.1 module has *no banner sections*. It is
one flat `verus!` block holding every definition's types and schema, followed by
one small private module per definition *outside* the block:

```rust,ignore
use vest_lib::asn1::der::{...};          // preamble selected by the encoding rules
verus! {

    // per definition: value type, abstract type, predicates, mappers,
    // combinator representations, and the nominal format type

} // verus!

mod __impl_kind   { use super::*; vest_lib::impl_der!(...); }
mod __impl_packet { use super::*; vest_lib::impl_der!(...); }
```

That last part is the biggest structural difference. Where the DSL writes out
`derived_specs`, `derived_proofs`, and `exec_impls` explicitly, the ASN.1
backend emits *one macro call per definition* and lets `vest_lib` expand the
specifications, proofs, and executable code.

## Value and abstract types

This matches the DSL closely — a value type and a generic
abstract type, bridged by `DeepView`:

```rust,ignore
pub struct Packet<'a> {
    pub kind: Kind,
    pub payload: Option<&'a [u8]>,
}

#[verifier::ext_equal]
pub struct PacketSpec<T0 = KindSpec, T1 = Option<Seq<u8>>> {
    pub kind: T0,
    pub payload: T1,
}

impl<'a> DeepView for Packet<'a> {
    type V = PacketSpec;
    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V { /* field-wise */ }
}
```

For a definition whose value type is already `Copy` and structural — an
`ENUMERATED`, for instance — there is no separate abstract type at all.

```rust,ignore
#[repr(i16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]
pub enum Kind { Request = 0, Response = 1 }

pub type KindSpec = Kind; // the abstract type is the same as the value type

impl DeepView for Kind { type V = Self; /* *self */ }
```

## Predicates and mappers

ASN.1 constraints become *named predicate structs* used in both the
specification and implementation, rather than the inline closures the DSL
emits:

```rust,ignore
#[derive(Clone, Copy)]
pub struct KindPredicate;

impl SpecPred<i16> for KindPredicate { /* value == 0 || value == 1 */ }
impl Pred<i16>     for KindPredicate { /* the executable test */ }
```

`ENUMERATED` values are built on the verified `i16` integer-content backend, which is
why the predicate is over `i16`. Larger enumerations are currently
[not yet supported](support.md).

Mappers follow the DSL's `Forward`/`Reverse` pattern, with one addition — they
implement the executable `Map` as well as `SpecMap`.

```rust,ignore
pub struct KindForward;
pub struct KindReverse;

impl SpecMap for KindForward { /* .. */ }
impl SpecMap for KindReverse { /* .. */ }
impl Map<i16> for KindForward { /* executable */ }
impl Map<Kind> for KindReverse { /* executable */ }
```

## The nominal format type

```rust,ignore
/// DER format for ASN.1 `Kind`.
type KIND__ = Mapped<Refined<Enumerated16TlvFmt, KindPredicate>, BiMap<KindForward, KindReverse>>;

#[derive(Clone, Copy)]
#[verifier::ext_equal]
pub struct KIND(pub Class, pub u64); // tag class, tag number

impl KIND {
    pub const Fmt: Self = Self(Class::Universal, 10u64);

    #[verifier::allow_in_spec]
    pub const fn schema() -> KIND__
        returns (Mapped { inner: Refined(ENUMERATED16, KindPredicate),
                          mapper: BiMap(KindForward, KindReverse) }),
    { /* the same representation */ }

    proof fn lemma_schema_unambiguous(&self) { /* .. */ }
}
```

Several things differ from the DSL here.

**The format type is always parametric.** `MessageFmt` in a DSL module is a zero-sized
struct. `KIND` is a tuple struct holding the effective tag class and number, so
an `IMPLICIT` tag can replace the outer tag without rebuilding the format.
`KIND::Fmt` is the associated constant carrying the definition's own tag —
`Class::Universal, 10` for `ENUMERATED`, `16` for `SEQUENCE`, etc.

**`schema()` is dual spec-exec.** The DSL's `spec_inner()` is
`pub open spec fn` — specification only. `schema()` here is a `const fn` marked
`#[verifier::allow_in_spec]` with a `returns` clause, so the same definition
serves both worlds (there are valid reasons for the DSL to separate them, such as to allow for more flexible executable implementations).

**`lemma_schema_unambiguous`** has no DSL counterpart. It proves the ASN.1 schema
unambiguous (needed for serialize-then-parse roundtrip) by leveraging a sound over-approximation of each ASN.1 combinator's parsing domain. On the other hand, the DSL's constructs disambiguate themselves largely by construction, so the DSL does not need to emit this lemma.

## Specifications, proofs, and executable code

Everything else arrives from one macro invocation, placed outside `verus!`:

```rust,ignore
mod __impl_packet {
    use super::*;
    vest_lib::impl_der!(
        tagged_exact(true),   // this definition contributes an outer tag
        borrowed,             // the value type borrows from the input
        PACKET, PACKET__,     // nominal type and its combinator type alias
        PacketSpec, Packet,   // abstract and executable value types
        PacketForward, PacketReverse
    );
}
```

`impl_der!` (or `impl_ber!` under BER) expands to the same code the DSL
emits explicitly — derived spec trait impls (`SpecParser`, `SpecSerializer`,
`SpecByteLen`, `Consistency`) and derived proof trait impls (`SafeParser`, `SoundParser`, `Productive`,
`NonTailFmt`, `GoodSerializer`, `NonMalleable`, etc.). Additionally, it also expands to the executable trait impls (`Parser`, `Prepare`, `Serializer`).

<!--## How this differs from DSL-generated code

| | Vest DSL | ASN.1 |
|---|---|---|
| File layout | five banner sections | flat `verus!` block + `mod __impl_*` after it |
| Spec/proof/exec code | written out in three private modules | one `impl_der!` / `impl_ber!` call per definition |
| Format type | `MessageFmt`, zero-sized | `PACKET(Class, u64)`, carries the effective tag |
| Entry value | `MessageFmt` | `PACKET::Fmt` associated constant |
| Combinator alias | `pub type MessageFmtSpec` | private `type PACKET__` |
| Constructor | `pub open spec fn spec_inner()` | dual `pub const fn schema()` |
| Abstract type | always a generic `*Spec` | identity alias when the value is already structural |
| Constraints | inline refinement closures | named `*Predicate` structs (`SpecPred` + `Pred`) |
| Mappers | `SpecMap` only | `SpecMap` **and** executable `Map` |
| Extra proofs | — | `lemma_schema_unambiguous`, `HasAsn1Start`, `DerOrd` |-->

## Calling it

Calling the parser, serializer, and the prepare methods is
almost identical in shape to DSL-generated code, except that the format value is the
`::Fmt` constant:

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

let (consumed, packet) = PACKET::Fmt.parse(&encoded).unwrap();

let size = PACKET::Fmt.prepare(&packet).unwrap();
let mut output = vec![0u8; size];
PACKET::Fmt.serialize(&packet, &mut output);
```
