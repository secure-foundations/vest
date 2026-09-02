# Enums

An enum is an integer on the wire with a name for each meaningful value. It corresponds to a Rust enum with the same discriminants. The generated Rust type is `#[repr(uN)]` where `N` is the backing width.

## Closed enums

```vest
message_type = enum {
    Request = 1,
    Response = 2,
    Error = 3,
}
```

This emits a `MessageType` Rust enum. Values must be distinct and fit the
inferred backing width.

**Parsing.** Reads the backing integer and maps it to a variant. Any other value
is a parse error.

**Preparation and serialization.** Preparation always succeeds and reports the
backing width. Serialization
writes the variant's discriminant as the backing integer.

## Open enums

Add `...` after the variants to preserve unknown values:

```vest
message_type = enum {
    Request = 1,
    Response = 2,
    ...
}
```

**Parsing.** A recognised value maps to its
variant, and anything else is kept as `Unknown(value)`.

**Preparation and serialization.** Same width as the closed form. Known variants serialize as before; `Unknown(value)` serializes as `value`.

## Choosing the backing width

The backing width is what actually determines how many bytes appear on the wire.
Without a suffix, Vest selects the smallest unsigned width containing every
value. A suffix on any enumerator fixes the type; all supplied suffixes must
agree:

```vest
wide_type = enum {
    Request = 1u16,
    Response = 2,
}
```

The supported executable backing widths are `u8`, `u16`, `u24`, `u32`, and
`u64`.

Inside a `bits` block, a suffix such as `0u3` instead selects a three-bit enum.
See [Bit fields](bits.md).
