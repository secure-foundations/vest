# Primitive formats

Primitive formats are the leaves from which larger formats are composed.

## Unsigned integers

A fixed-width big- or little-endian integer.

```vest
!BIG_ENDIAN

header = {
    kind: u8,
    length: u16,
    sequence: u24,
    timestamp: u32,
    nonce: u64,
}
```

`u8`, `u16`, `u24`, `u32`, and `u64` are supported. Multi-byte integers follow the file's byte order.
The generated Rust types are the matching
unsigned integer types, except that `u24` is represented as `u32` (with proper value constraints specified in Verus).

**Parsing.** Reads exactly the declared number of bytes and interprets them in the specified byte order. Fewer bytes remaining than the width is a parse error.

**Preparation and serialization.** Preparation always succeeds and reports the
fixed width. Serialization writes that many bytes in the same byte order.

Signed counterparts are supported in the `vest_lib` backend, but not yet exposed in the DSL (currently rejected during type checking, but we plan to support them soon).
Widths other than the five listed above are rejected too. See [bitfields](bits.md) for ways to specify bit-sized integers inside a `bits` block.

## Variable-width integers

`btc_varint` is Bitcoin's CompactSize unsigned integer and maps to `u64` in Rust. The
encoding is one byte for small values and a tagged 3-, 5-, or 9-byte form
otherwise, so its width depends on the value.

```vest
input = {
    flags: u8,
}

transaction_prefix = {
    @input_count: btc_varint, // 1, 3, 5, or 9 bytes
    inputs: [input; @input_count],
}
```

**Parsing.** Reads the leading tag byte, then the remaining bytes according to the tag. Interprets the result as a `u64`.
Only the *shortest* encoding of a value is accepted — a value padded into a
wider form is rejected, which is what keeps the format non-malleable.

**Preparation and serialization.** Preparation reports the width of the shortest encoding for that value. Serialization writes exactly that form.

The `vest_lib` backend also supports other variable-length integers such as `uleb128`, `base128` (VLQ), and `base256`. We plan to expose them in the DSL soon.

## Bytes and arrays

`[u8; length]` is a run of raw bytes of a known length, mapping to a Rust byte slice (`&[u8]`) to avoid unnecessary copying.

```vest
digest = [u8; 32]
```

**Parsing.** Takes exactly `length` bytes and borrows them from the input.

**Preparation and serialization.** Preparation checks that the slice is exactly
`length` bytes long and reports that length; a slice of any other size is an
error. Serialization copies the bytes through unchanged.

For non-byte elements, `[format; count]` is a repeated format, and a constant
count produces a Rust array:

```vest
words = [u16; 8]
```

Lengths and counts may also use runtime dependencies and arithmetic; see
[Structures and dependencies](structs.md), and
[Collections](collections.md) for the repetition semantics.

## `Tail`, `Nothing`, and `Never`

```vest
payload = {
    header: u16,
    rest: Tail,
}

empty = Nothing
reject = Never("this branch is reserved")
```

| Format | Meaning | Parsing | Preparation and serialization |
|---|---|---|---|
| `Tail` | "whatever is left" | consumes all remaining input and borrows it | reports the slice length; writes the bytes through |
| `Nothing` | the empty format | consumes nothing, yields `()` | reports length 0; writes nothing |
| `Never("msg")` | the impossible format | always fails with `msg` | unreachable — its value type is uninhabited |

`Tail` can be used to "under-specify" a format, leaving the rest of the input uninterpreted.
`Nothing` can be used as the "do-nothing" branch of a choice;
`Never` marks a branch that must never be taken,
and gives the resulting parse error a message you choose.
See [Choices](choices.md).
