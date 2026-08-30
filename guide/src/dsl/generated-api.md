# Generated Rust API

For a definition named `message`, Vest normally emits:

- `Message` and `MessageSpec`, the executable and logical value types;
- `MessageFmt`, the nominal verified format;
- implementations of `Parser`, `Prepare`, `ByteLen`, and `Serializer`; and
- specification and proof-trait implementations used by enclosing formats.

Generated structs borrow fixed and variable byte regions from their input when
the wire format permits zero-copy parsing. Collections and formats that must
combine fragmented input use owned values and therefore require the `alloc`
feature.

## Parsing

`MessageFmt.parse(&input)` returns `(consumed, value)`. Success is proved to
match the pure `spec_parse` result. Parsing does not require that the entire
input be consumed unless the format itself ends with an end-of-input
combinator.

## Preparation and serialization

Call `MessageFmt.prepare(&value)` before serializing. It checks constants,
dependent lengths, predicates, choices, recursion limits, and other consistency
conditions, then returns the exact output length. Allocate or borrow a slice of
that length and call `MessageFmt.serialize(&value, output)`.

For advanced streaming code, `Serializer::serialize_into` targets any
`OutputBuf`, including a growable `Vec<u8>` or an `OutputSlice`. The convenience
slice API is preferred when the final length is known.

## Errors and generated files

Parsing returns a `ParseError`; preparation returns a `PreSerializeError`.
Named formats preserve a nested format trace when allocation is enabled.
Generated files are deterministic build artifacts and should be regenerated,
not edited manually.

The exact executable contracts are documented under
[`core::exec`](https://secure-foundations.github.io/vest/vest_lib/core/exec/).

