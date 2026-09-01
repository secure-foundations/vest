# Generated Rust Code

Vest emits one user-facing value type and one format type for each named DSL
definition. It also emits specification, proof, and executable helpers/trait implementations. The
helpers are public to ease the codegen plumbing,
but application
code normally needs only the value and format types.

For this definition:

```vest
message = {
    @length: u16,
    payload: [u8; @length],
}
```

the user-facing types are:

```rust,ignore
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Message<'i> {
    pub length: u16,
    pub payload: &'i [u8],
}

pub struct MessageFmt;
```

## The shape of an emitted file

The whole module is a single `verus!` block behind a fixed `use` preamble, cut
into five banner-delimited sections:

```rust,ignore
use vest_lib::combinators::*;            // fixed preamble, identical in every file
use vest_lib::core::exec::parser::*;
// ...
verus! {

// ============================================================
// Data Types
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

A file with nine definitions emits
all nine value types, then all nine nominal format types, then all the derived
specifications, and so on.
Because the nominal format types (e.g., `MessageFmt`) are what the user actually interacts with,
the last three sections are wrapped in private
modules (`derived_specs`, `derived_proofs`, `exec_impls`).

## Data Types

Per definition, alongside the `Message` shown above, Vest emits a nominal abstract value type
(`MessageSpec`) and a structural representation (`MessageInner`), plus the
`DeepView` impl that converts between the executable value and the abstract value. Additionally, Vest emits two empty structs (`MessageForward` and `MessageReverse`)
to name the bijective conversion between the structural and nominal abstract value types.

```rust,ignore
#[verifier::ext_equal]
pub struct MessageSpec<T0 = u16, T1 = Seq<u8>> {   // abstract view of Message
    pub length: T0,
    pub payload: T1,
}

pub type MessageInner = (u16, Seq<u8>);           // what the combinator tree yields

impl<'i> DeepView for Message<'i> {               // exec value -> abstract value
    type V = MessageSpec;
    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V { /* field-wise */ }
}

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

For a `choose`, the same set appears with `enum` instead of `struct`, and
`MessageInner` becomes nested `Sum`s rather than a nested tuple.

## Format Specifications

This section is the format combinator representation (defined in `vest_lib`) of the DSL definition.

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

Note how each DSL construct has a corresponding shape in the combinator representation (`@length: u16` becomes `Bind(U16Le, |length: u16| ...)`, `[u8; @length]` becomes `Varied(length)`, etc.). The `Named` wrapper is what gives the format a human-readable name for error reporting.

## Derived Specifications

Because `spec_inner()` is a combinator tree composed of `vest_lib` format combinators, we can _derive_ the formal specifications of the format from it.

```rust,ignore
impl SpecParser        for MessageFmt { type PVal   = MessageSpec; /* spec_parse */ }
impl Consistency       for MessageFmt { type Val    = MessageSpec; /* consistent */ }
impl SpecSerializer    for MessageFmt { type SVal   = MessageSpec; /* spec_serialize */ }
impl SpecByteLen       for MessageFmt { type T      = MessageSpec; /* byte_len */ }
```

Every method body is literally `Self::spec_inner().<method name>(..)`.
Most of them are marked
`#[verifier::opaque]` so enclosing formats cannot see their inner definitions.
This opacity is what keeps verification cost
from exploding as formats grow in size and complexity.

## Proven Format Properties

Likewise, the proofs of format properties are _mostly_ derived from `spec_inner()`.

```rust,ignore
broadcast use {
    vest_lib::combinators::disjoint::disjointness_lemmas,
    MessageSpec::lemma_from_into,
    MessageSpec::lemma_into_from,
};

impl SafeParser  for MessageFmt { /* .. */ }
impl Productive  for MessageFmt { /* .. */ }
impl SoundParser for MessageFmt { /* .. */ }
impl SPRoundTrip for MessageFmt { /* .. */ }
impl NonMalleable for MessageFmt { /* .. */ }
// ...plus more auxiliary proof traits, depending on the format
```

Each proof reveals the opaque specifications it needs, then hands off to the
corresponding lemma on `spec_inner()`. `disjointness_lemmas` is a broadcast group of lemmas that compositionally establish the non-ambiguity of certain format combinators, which is a prerequisite for serialize-then-parse round trips.

## Executable Implementations

Finally, the executable implementations of `Parser`, `Serializer`, and `Prepare` are emitted.
Here, the implementations are _not_ derived from `spec_inner()`; they are written in idiomatic imperative Rust to ensure performance and avoid unnecessary combinator overhead.

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

`parse` walks the fields, advancing a cursor and propagating failure with `?`,
then assembles the value and asserts it matches `spec_parse`:

```rust,ignore
let (n1, length)  = U16Le.parse(&rest)?;
let rest          = rest.skip(n1);
let (n2, payload) = Varied(length).parse(&rest)?;
// ...
Ok((n1 + n2, Message { length, payload }))
```

`serialize_into` mirrors it — it traverses the value and writes each field directly in-place to the outbuf buffer. `prepare` similarly walks the value, checking that each field is valid and summing the lengths.

## Calling it

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

let input: &[u8] = &[3, 0, b'a', b'b', b'c'];
let (consumed, message) = MessageFmt.parse(&input).unwrap();
assert_eq!(consumed, 5);
assert_eq!(message.payload, b"abc");

let length = MessageFmt.prepare(&message).unwrap();
let mut output = vec![0u8; length];
MessageFmt.serialize(&message, &mut output);
```

`parse` returns the consumed prefix length and the value; it need not consume
the whole input unless the format says so. Errors carry a `ParseErrorKind` along with the static identifier provided to the `Name` combinator. When the `alloc` feature is enabled, the error also builds a trace of the enclosing formats, which is useful for debugging.
<!--with allocation enabled the `Named` wrappers build a trace of the enclosing
formats.-->

The `SerializerExt` trait provides two convenience methods for serializing values into a buffer: `serialize` and `serialize_with_vec`.
`serialize` writes into an exactly sized
slice and `serialize_with_vec` appends to a growable `Vec<u8>`. In both cases, the length of the buffer can be obtained from `prepare` to provably avoid (re)allocation.
