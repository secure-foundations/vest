# Generated Rust Code

This page is the reference for the Rust/Verus code that Vest emits from a DSL definition.
It first takes a complete tour of a generated file, then covers
the API for calling the generated code and for reasoning about it in Verus.

We'll use a variable-length message format as the running example. The DSL definition is

```vest
message = {
    @length: u16,
    payload: [u8; @length],
}
```

Compiling `src/message.vest` to `src/message.rs` gives these two user-facing types:

```rust,ignore
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Message<'i> {
    pub length: u16,
    pub payload: &'i [u8],
}

pub struct MessageFmt;
```

If you are only interested in invoking the generated code, you can skip ahead to
[Calling the generated code](#calling-the-generated-code).

## Inside the generated file

### The shape of an emitted file

The file starts with a comment identifying the `vest` compiler version and
warning against manual edits: change the `.vest` source and regenerate instead.
The whole module is a single `verus!` block behind a fixed `use` preamble. It is
divided into six sections:

```rust,ignore
use vest_lib::prelude::*;                // common APIs, combinators, and Verus prelude
// ...additional imports for generated mapping and recursion helpers
verus! {

// ============================================================
// Data Types
// ============================================================
// ============================================================
// Structural Mappers
// ============================================================
// ============================================================
// Format Specifications
// ============================================================
// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
// ============================================================
// Proven Format Properties
// ============================================================
// ============================================================
// Executable Implementations
// ============================================================

} // verus!
```

Each section covers every definition in the file. A file with nine definitions
emits all nine value types, then all nine nominal format types, then all the
derived specifications, and so on. The last three sections only implement
traits for the format types, so they are wrapped in private modules
(`derived_specs`, `derived_proofs`, and `exec_impls`).

The compiler pretty prints its output in the style of `rustfmt`/`verusfmt`, so generated files need no separate formatting pass
(in fact, `verusfmt` would hang on those deeply nested combinator expressions that the compiler emits).

### Data Types

Besides `Message`, Vest emits an abstract value type (`MessageSpec`), a
structural representation (`MessageInner`), and a `DeepView` implementation
that maps the executable value to its abstract value:

```rust,ignore
#[verifier::ext_equal]
pub struct MessageSpec<T0 = u16, T1 = Seq<u8>> {   // abstract view of Message
    pub length: T0,
    pub payload: T1,
}

pub type MessageInner = (u16, Seq<u8>);           // what the Vest combinators operate on

impl<'i> DeepView for Message<'i> {               // exec value -> abstract value
    type V = MessageSpec;
    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V { /* field-wise */ }
}
```

`MessageSpec` has the same fields as `Message`, but the borrowed payload becomes
a `Seq<u8>`. Vest specs and proofs talk about these abstract values.

### Structural Mappers

The `vest_lib` combinators operate on the structural representation (`MessageInner`),
while the "view" of `Message` is the more ergonomic nominal type `MessageSpec`.
This section converts between the two. It also declares two empty structs, `MessageForward` and
`MessageReverse`, which name the conversion for the `Mapped` combinator:

```rust,ignore
impl<T0, T1> MessageSpec<T0, T1> {                // abstract value <-> nested tuple
    #[verifier::opaque] pub open spec fn from_structural(input: (T0, T1)) -> Self { /* .. */ }
    #[verifier::opaque] pub open spec fn into_structural(self) -> (T0, T1) { /* .. */ }
    pub proof fn lemma_from_into(self) { /* .. */ }
    pub proof fn lemma_into_from(input: (T0, T1)) { /* .. */ }
}

// The bijection between the structural tuple and the nominal abstract value
#[doc(hidden)] pub struct MessageForward;
#[doc(hidden)] pub struct MessageReverse;
```

For a `choose`, the same items appear with `enum` instead of `struct`, and
`MessageInner` becomes nested `Sum`s rather than a nested tuple.

### Format Specifications

`spec_inner()` describes the DSL definition as a tree of `vest_lib` format
combinators:

```rust,ignore
pub type MessageFmtSpec =
    Named<Mapped<Bind<U16Le, spec_fn(u16) -> Varied<u16>>, BiMap<MessageForward, MessageReverse>>>;

impl MessageFmt {
    pub open spec fn spec_inner() -> MessageFmtSpec {
        Named("message", Mapped {
            inner: Bind(U16Le, |length: u16| Varied(length)),
            mapper: BiMap(MessageForward, MessageReverse),
        })
    }
}
```

Each DSL construct has a matching combinator: `@length: u16` becomes
`Bind(U16Le, |length: u16| ...)`, and `[u8; @length]` becomes `Varied(length)`.
The `Named` wrapper gives the format a human-readable name for error reporting.

### Derived Specifications

Because `spec_inner()` is built from `vest_lib` combinators, the format's formal
specifications can be *derived* from it:

```rust,ignore
impl SpecParser        for MessageFmt { type PVal   = MessageSpec; /* spec_parse */ }
impl Consistency       for MessageFmt { type Val    = MessageSpec; /* consistent */ }
impl SpecSerializer    for MessageFmt { type SVal   = MessageSpec; /* spec_serialize */ }
impl SpecByteLen       for MessageFmt { type T      = MessageSpec; /* byte_len */ }
```

For `MessageFmt`, the parser, serializer, and byte-length specs are marked
`#[verifier::opaque]`, while value consistency spec is transparent. Together with the
opaque `deep_view`, these define what a verified client can see by default.
A proof can reveal the public length calculation without opening the structural conversion or the
parser and serializer specs, as we'll see in
[Concrete fields and byte lengths](#concrete-fields-and-byte-lengths).

### Proven Format Properties

The proofs of format properties are also *mostly* derived from `spec_inner()`:

```rust,ignore
broadcast use {
    vest_lib::combinators::disjoint::disjointness_lemmas,
    MessageSpec::lemma_from_into,
    MessageSpec::lemma_into_from,
};

impl SafeParser  for MessageFmt { /* .. */ }
impl Productive  for MessageFmt { /* .. */ }
impl SoundParser for MessageFmt { /* .. */ }
impl SPRoundTripDps for MessageFmt { /* .. */ }
impl NonMalleable for MessageFmt { /* .. */ }
// ...plus more auxiliary proof traits, depending on the format
```

Each proof reveals the opaque specifications it needs, then hands off to the
corresponding lemma on `spec_inner()`. `disjointness_lemmas` is a broadcast
group of lemmas that compositionally establish that certain combinators are
unambiguous, which serialize-then-parse roundtrips require.

You won't find emitted implementations of `SPRoundTrip`, `PSRoundTrip`, or
`NonAmbiguous`: the library derives them once-and-for-all from the generated proof traits through
blanket implementations. Together, these traits provide the theorems that client
proofs call:

- `theorem_serialize_parse_roundtrip` comes from `SPRoundTrip`.
- `theorem_parse_serialize_roundtrip` comes from `PSRoundTrip`.
- `lemma_parse_non_malleable` comes from `NonMalleable`.
- `lemma_serialize_injective` comes from `NonAmbiguous`.

### Executable Implementations

Finally, the file implements the executable `Parser`, `Serializer`, and
`Prepare` traits. These implementations are *not* derived from `spec_inner()`.
They are written as idiomatic imperative Rust, which keeps them fast and avoids
any potential combinator overhead:

```rust,ignore
impl<'i> Parser<&'i [u8]> for MessageFmt {
    type PT = Message<'i>;
    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> { /* .. */ }
}

impl<Output: OutputBuf, 'i> Serializer<Output, Message<'i>> for MessageFmt {
    fn serialize_into(&self, v: &Message<'i>, obuf: &mut Output) { /* .. */ }
}

impl<'i> Prepare<Message<'i>> for MessageFmt {
    fn prepare(&self, v: &Message<'i>) -> Result<usize, PreSerializeError> { /* .. */ }
}
```

`parse` walks the fields, advancing a cursor and propagating failure with `?`.
It then assembles the value and asserts that it matches `spec_parse`:

```rust,ignore
let (n1, length)  = U16Le.parse(&rest)?;
let rest          = rest.skip(n1);
let (n2, payload) = Varied(length).parse(&rest)?;
// ...
Ok((n1 + n2, Message { length, payload }))
```

`serialize_into` walks the same fields, writing each one directly into the output
buffer. `prepare` walks them to check consistency and add up their lengths.

## Calling the generated code

From ordinary Rust, you call these implementations through traits in
`vest_lib::core::exec`:

| Call | Trait | What it does |
| --- | --- | --- |
| `MessageFmt.parse(&input)` | `Parser` | Parses a prefix of `input` and returns `(consumed, value)`. Byte fields such as `payload` borrow from `input`. |
| `MessageFmt.prepare(&value)` | `Prepare` | Checks that `value` is consistent with the format (here, that `length` equals the payload size) and returns its exact wire length. |
| `MessageFmt.serialize(&value, &mut output)` | `SerializerExt` | Writes a consistent value into a buffer of exactly that length, without failing or allocating. |
| `MessageFmt.serialize_with_vec(&value, &mut vec)` | `SerializerExt` | Appends a consistent value to a growable `Vec<u8>`, which may reallocate. To avoid growth, reserve the length returned by `prepare` first. |

Neither serializer rechecks consistency, so unverified code must call `prepare`
first; see [Serializing a message](../getting-started.md#serializing-a-message).

Failures return a `ParseError` or a `PreSerializeError`. Each records the kind
of failure and the innermost named format that reported it. Enable
`vest_lib`'s `error-trace` feature to also keep the trace of enclosing formats.

## Reasoning about generated values

We've seen that the [getting-started example](../getting-started.md#using-vest-from-verified-rust)
proves a value serialize-parse roundtrip. This section further covers:

- what each executable API guarantees,
- how to prove facts about fields and lengths,
- and which theorems relate parsing and serialization.

The examples belong inside a `verus!` block. They use `crate::message::*` and
`vest_lib::prelude::*`. The prelude brings the executable APIs, specification
and proof traits, format combinators, and the Verus prelude into scope.

### Values and API contracts

| API | Pre/post-conditions |
| --- | --- |
| `parse(&input)` | It behaves exactly like `spec_parse(input@)` (on both success and failure). |
| `prepare(&value)` | On `Ok(n)`, `value` is consistent with the format and `n == byte_len(value.deep_view())`. |
| `serialize(&value, &mut output)` | Requires value consistency and an exactly sized buffer; afterward, `output@ == spec_serialize(value.deep_view())`. |

`vest_lib`'s broadcast group `basic_lemmas` covers some basic useful facts about byte buffers and serialization lengths, which apply automatically when `vest_lib::prelude::*` is in scope.

For more facts about parsed values, enable `parser_lemmas` in the function or proof that needs them:

```rust,ignore
broadcast use parser_lemmas;
```

These lemmas tell Verus three things about a successful parse: it stays within the input buffer,
it produces a value consistent with the format, and it consumes exactly that value's
`byte_len`. Roundtrip and non-malleability theorems still have to be called
explicitly.

### Concrete fields and byte lengths

To prove facts about individual fields or concrete lengths, use Verus's `reveal` to open the view and length definitions.
This function builds a message, serializes it, parses it back, and proves the
exact length and field values:

```rust,ignore
fn check_message() -> Result<(), PreSerializeError> {
    let value = Message { length: 3, payload: &[0xCA, 0xFE, 0x42] };
    proof {
        reveal(<Message as DeepView>::deep_view);
        reveal(<MessageFmt as SpecByteLen>::byte_len);
    }
    let len = MessageFmt.prepare(&value)?;
    assert(len == 5); // 2 length bytes + 3 payload bytes

    let mut output = vec![0u8; len];
    MessageFmt.serialize(&value, &mut output);
    proof {
        MessageFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = MessageFmt.parse(&output.as_slice()).unwrap();
    assert(consumed == 5);
    assert(parsed.length == 3);
    assert(parsed.payload@ == seq![0xCAu8, 0xFE, 0x42]);
    Ok(())
}
```

The first `reveal` connects the Rust fields to their logical counterparts, and
the second exposes the length calculation. Without either one, Verus can't prove
the assertions. The roundtrip theorem says that `parsed` has the same deep view
as `value`, and the revealed view turns that into the concrete field values.

Both definitions are opaque by default, which keeps proofs about deeply nested
formats manageable. Here, only the public view and length are opened. The parser
and serializer specifications stay closed, and the internal structural representation
never needs to be revealed.

For a nested format, reveal a child type's view only when you need to reason about that child's
fields; its format specifications can stay closed.

*Fixed-length* formats need even less proof code. When the compiler can determine
a fixed length, it emits a verified `StaticByteLen` implementation for the format.
For example, compile these definitions to
`src/lengths.rs`:

```vest
triple = {
    a: u8,
    const b: [u8; 2] = [0x55, 0x77],
    c: u64,
}

samples = {
    @count: u16,
    values: [u16; @count],
}
```

Here, a prepared `Triple` takes 11 bytes (`1 + 2 + 8`), and proving it needs no reveals:

```rust,ignore
fn fixed_length(value: &Triple) -> Result<usize, PreSerializeError> {
    let len = TripleFmt.prepare(value)?;
    assert(len == 11);
    Ok(len)
}
```

`Samples` has a variable length, but each element is a fixed-width `u16`. After
the usual reveals, we can assert that the length is `2 + 2 * count`:

```rust,ignore
fn samples_length(value: &Samples) -> Result<usize, PreSerializeError> {
    proof {
        reveal(<Samples as DeepView>::deep_view);
        reveal(<SamplesFmt as SpecByteLen>::byte_len);
    }
    let len = SamplesFmt.prepare(value)?;
    assert(len == 2 + 2 * value.values@.len());
    Ok(len)
}
```

`vest_lib` also provides the `ByteLen::length` API for infallible length calculation, but the DSL doesn't
currently generate it. Unlike `prepare`, `length` doesn't check consistency, and
it needs a proof that the length fits in `usize`.

### Roundtrips and non-malleability

The getting-started example proves facts in the direction of value --> bytes --> value, leveraging `theorem_serialize_parse_roundtrip`.
`theorem_parse_serialize_roundtrip` goes the other way, from bytes --> value --> bytes. It is useful for re-encoding a message:

```rust,ignore
fn reencode(input: &[u8]) -> Result<Vec<u8>, ParseError> {
    broadcast use parser_lemmas;

    let (consumed, value) = MessageFmt.parse(&input)?;
    let mut output = vec![0u8; consumed];
    MessageFmt.serialize(&value, &mut output);
    proof {
        MessageFmt.theorem_parse_serialize_roundtrip(input@);
    }
    assert(output@ == input@[0..consumed]);
    Ok(output)
}
```

Note that no `prepare` is needed here. `parser_lemmas` already establish that `value` is
consistent with the format and that `consumed` is its exact length. The equality covers only the consumed prefix.
It also inherently requires non-malleability: a malleable format, such as ASN.1 BER, may accept
several encodings of the same value during parsing and serialize it to a different binary form.

See the [proof traits](../../vest_lib/core/proof/index.html) in `vest_lib` for more details on the roundtrip and non-malleability theorems.
