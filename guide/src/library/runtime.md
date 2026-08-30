# Parsing and serialization

The executable API follows one lifecycle:

1. `Parser::parse` reads an input buffer and returns the consumed length and
   value.
2. `Prepare::prepare` checks that a value is serializable and returns its exact
   length.
3. `SerializerExt::serialize` writes into an exactly sized caller-provided
   slice.

```rust,ignore
use vest_lib::combinators::U16Be;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

let input: &[u8] = &[0x12, 0x34];
let (consumed, value) = U16Be.parse(&input).unwrap();
assert_eq!((consumed, value), (2, 0x1234));

let len = U16Be.prepare(&value).unwrap();
let mut output = vec![0; len];
U16Be.serialize(&value, output.as_mut_slice());
assert_eq!(output, input);
```

Parsers accept any input type implementing the slice-oriented `InputBuf`
interface. Serializers target `OutputBuf`; `OutputSlice` provides bounded,
allocation-free output and `Vec<u8>` provides growable output when `alloc` is
enabled. `write_bytes` copies whole regions directly for both standard output
implementations.

Preparation is the fallible boundary. Once it succeeds, the value is proved
consistent and the returned size agrees with the specification, allowing the
serializer itself to be infallible.

See the exact contracts for
[`Parser`](https://secure-foundations.github.io/vest/vest_lib/core/exec/parser/trait.Parser.html),
[`Prepare`](https://secure-foundations.github.io/vest/vest_lib/core/exec/serializer/trait.Prepare.html),
and
[`Serializer`](https://secure-foundations.github.io/vest/vest_lib/core/exec/serializer/trait.Serializer.html).
