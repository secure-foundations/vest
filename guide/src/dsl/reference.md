# Vest language reference

Vest source files contain named format definitions, optional parameters,
constants, macros, and one byte-endianness directive. Definitions are compiled
to Verus/Rust value types, format wrappers, specifications, proofs, and
executable implementations.

## Primitive formats

- `u8`, `u16`, `u24`, `u32`, `u64` and their signed counterparts use the file's
  `!BIG_ENDIAN` or `!LITTLE_ENDIAN` directive where byte order applies.
- `btc_varint` is Bitcoin's variable-width integer and `uleb128` is unsigned LEB128.
- `[u8; n]` is a byte string of the given length; `[fmt; n]` is a fixed or
  dependency-sized repetition.
- `Tail` consumes the remaining input. `Nothing` consumes no bytes, while
  `Never("reason")` rejects every input.

Integer formats may be refined with a value, range, set, or complement, such
as `u16 | 1..1024` or `u8 | !{0, 255}`.

## Structures and dependencies

```vest
message = {
    @kind: message_type,
    @len: u16,
    body: [u8; @len] >>= choose(@kind) {
        Request => request,
        Response => response,
    },
}
```

Ordinary fields become fields of the generated value type. A name prefixed by
`@` may be referenced by later formats and length expressions. A constant field
is checked on input and reconstructed during serialization without appearing
in the logical value.

`lhs >>= rhs` parses `lhs`, restricts `rhs` to the resulting region where
applicable, and returns the value of `rhs`. Length expressions support constants,
dependencies, parentheses, `+`, `-`, `*`, `/`, and `|format|` for static width.

## Choices, enums, and collections

- `enum { Name = value, ... }` defines a typed integer enumeration. A trailing
  `...` preserves unknown values.
- `choose { Variant => fmt, ... }` defines an ordered choice with a nominal
  enum value.
- `choose(@tag) { ... }` dispatches using an earlier dependency. `_` is the
  fallback branch.
- `Option<fmt>` accepts zero or one value and `Vec<fmt>` accepts zero or more.
  Their placement must leave parsing unambiguous and productive.

## Wrapping, bitfields, and macros

`wrap(...)` surrounds a value format with fixed integer, enum, or byte
constants. `bits { ... }` packs integer fields into a fixed-width carrier; the
file endianness controls byte order, while fields are laid out from the most
significant bit of the carrier.

Format macros use `macro name!(...) = ...` and are expanded before type
checking. Named formats may take dependency parameters using
`name(@parameter: format) = ...`.

## Recursion and limitations

Vest supports generated bounded recursive formats through the backend's
fixpoint combinators. Mutual-recursion code generation remains experimental and
is not part of the default verified fixture set. The compiler reports syntax,
type, dependency, productivity, and proof-composition problems rather than
silently changing the wire format.

Run `vest --help` for the current command-line interface. The parser grammar is
available in
[`vest/src/vest.pest`](https://github.com/secure-foundations/vest/blob/main/vest/src/vest.pest),
and the checked-in `.vest` fixtures are the executable reference for supported
combinations.
