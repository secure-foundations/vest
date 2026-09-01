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

`wrap` surrounds a format with fixed bytes that carry no information — a magic
prefix, a terminator — and keeps them out of the value.

```vest
framed_word = wrap(
    u8 = 0xAA,
    u16,
    [u8; 2] = [0x0D, 0x0A]
)
```

The generated value is just `u16`.

**Parsing.** Requires the prefix constants, parses the inner format, then
requires the suffix constants. A constant that does not match is a parse error.
The framing bytes are consumed but discarded.

**Preparation and serialization.** Preparation reports the inner length plus the
widths of all the constants. Serialization writes the prefix, the inner value,
and the suffix — the constants are restored from the format, since they were
never in the value.

This is the difference from a `const` structure field, which stays part of the
generated struct and must be supplied by the caller.

`wrap` accepts any number of constant integer, byte-string, or enum formats
before and after its one non-constant inner format.

## Parameterized formats

Parameters are values supplied by the enclosing format:

```vest
payload(@length: u16) = [u8; @length]

packet = {
    @length: u16,
    body: payload(@length),
}
```

**Parsing and preparation.** A parameter contributes no bytes of its own. It
behaves exactly like a dependency that happens to be bound outside: it sizes or
selects during parsing, and is enforced as a constraint during preparation.

Arguments must be `@` dependencies in scope and must match the declared
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
