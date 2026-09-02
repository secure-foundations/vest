# Composition

## Format aliases

A definition may directly reuse another format:

```vest
header = { kind: u8, length: u16, }
header_alias = header
```

The alias receives its own generated format name while using the referenced
value type. Parsing, preparation, and serialization are those of the referenced
format; the alias adds no wire bytes.

## Framing with `wrap`

`wrap` surrounds a format with fixed bytes that carry no semantic information (e.g., a magic
prefix, a terminator, or padding) and keeps them out of the value.

```vest
framed_word = wrap(
    u8 = 0xAA,
    u16,
    [u8; 2] = [0x0D, 0x0A]
)
```

The generated value type for `framed_word` is just `u16`.

**Parsing.** Recognizes the prefix constants, parses the inner format, then
recognizes the suffix constants. A constant that does not match is a parse error.
The framing bytes are consumed but discarded.

**Preparation and serialization.** Preparation reports the inner length plus the
widths of all the constants. Serialization writes the prefix, the inner value,
and the suffix.

This is the difference from a `const` structure field, which stays part of the
generated struct and must be supplied by the caller during preparation and serialization.

`wrap` accepts any number of constant integer, byte-string, or enum formats
before and after its one non-constant inner format.

## Parameterized formats

```vest
payload(@length: u16) = [u8; @length]

packet = {
    @length: u16,
    body: payload(@length),
}
```

Parameters are *values* supplied by the enclosing format. They are not part of the generated value type.

**Parsing and preparation.** A parameter contributes no bytes of its own. It
behaves exactly like a dependency but is required to be bound *externally* in the enclosing format.

When invoked, arguments must be `@` dependencies in scope and must match the declared
parameter format.

## Macros

Macros substitute format arguments before type checking:

```vest
macro length_prefixed!(length_format, body_format) = {
    @length: length_format,
    body: [u8; @length] >>= body_format,
}

words = length_prefixed!(u16, Vec<u32>)
```

Macro arguments are format expressions. Macros are purely syntactic and
have no semantics of their own. The expansion behaves exactly as if you had
written it out.
