# Structures and dependencies

A struct is a fixed sequence of fields laid out back to back on the wire (without padding). The DSL
generates a Rust struct with the same field names, in the same order.

```vest
record = {
    kind: u8,
    flags: u16,
    payload: [u8; 8],
}
```

Every field is followed by a comma, including the last one.

**Parsing.** Parses each field in definition order. The bytes consumed are the sum of the fields' wire lengths.
The parsed value is `Record { kind, flags, payload }`.

**Preparation and serialization.** Preparation prepares each field, adds up the
lengths with an overflow check, and fails if any field fails. Serialization
writes the fields in the same order, back to back.

## Dependency fields

Prefix a field name with `@` to let later fields refer to its value:

```vest
packet = {
    @length: u16,
    payload: [u8; @length],
}
```

The generated value is `Packet { length, payload }`. The `@` field is present on the wire and in the Rust value.

**Parsing.** `@length` is parsed like any other field; its value is then in
scope, so `[u8; @length]` knows how many bytes to take.

**Preparation and serialization.** The direction reverses: `@length` is now a
consistency requirement. Preparation checks that the payload really is `length` bytes and
fails otherwise. Serialization then writes
both fields normally.

A dependency may refer only to a preceding field or a format parameter. Dotted
field access is supported for nested structs:

```vest
header = {
    kind: u8,
    payload_length: u32,
}

framed = {
    @header: header,
    body: [u8; @header.payload_length],
}
```

## Constant fields

A field whose value is fixed by the format — a magic number or version byte:

```vest
message = {
    const version: u8 = 1,
    const magic: [u8; 4] = "vest",
    body: Tail,
}
```

**Parsing.** Reads the field and requires it to equal the declared constant;
anything else is a parse error.

**Preparation and serialization.** Constant fields are still present in the
generated struct, so preparation rejects a caller value whose field differs, and
serialization writes the declared bytes. Use
[`wrap`](composition.md#framing-with-wrap) when framing constants should be
absent from the value type entirely.

Top-level constants can name byte, integer, or enum constants for reuse:

```vest
const MAGIC: [u8; 4] = "vest"

message = {
    const magic: MAGIC,
    body: Tail,
}
```

## Length expressions

Array and byte-string lengths support integer literals, dependencies, static
format sizes, parentheses, and arithmetic:

```vest
header = {
    @total: u16 | 8..,
    flags: u8,
}

body(@header: header) = {
    payload: [u8; @header.total - |header|],
}
```

`|format|` is the static encoded size of a fixed-width named or primitive
format. It is rejected for dynamically sized or parameter-dependent formats.

**Parsing and preparation.** The expression is evaluated the same way in both
directions — to decide how many bytes to read, and to check how many bytes a
value must occupy. The arithmetic is checked for overflow and underflow in the
executable code (statically by Verus for parsing, and at runtime for preparation).
