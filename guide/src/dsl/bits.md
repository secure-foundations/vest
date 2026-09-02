# Bit fields

`bits { ... }` describes several small unsigned fields packed into one
fixed-width integer on the wire. The block as a whole is a single integer; the fields are slices of its bits.
The DSL compiler exposes them as ordinary integer-typed Rust
fields.

```vest
ipv4_first_byte = bits {
    version: u4,
    ihl: u4,
}
```

Fields are laid out from the *most significant bit* of the integer, in declaration
order. The total width must be exactly 8, 16, 24, 32, or 64 bits; otherwise the
compiler reports an invalid total width. Each individual width must be positive
and no larger than 64.

**Parsing.** Reads the integer according to the specified byte order, then splits it into fields from the most significant bit
down, and checks each field's constraint.

**Preparation and serialization.** Preparation checks that each field fits its
declared bit width and satisfies its constraint, and reports the integer's width.
Serialization packs the fields back into one integer and writes it in the specified byte order.

## Cross-byte fields and byte order

```vest
!BIG_ENDIAN

packed = bits {
    prefix: u3,
    value: u10,
    suffix: u3,
}
```

Fields may straddle byte boundaries; only the integer as a whole is required to be byte
aligned. Byte endianness controls how that multi-byte integer is decoded/encoded.
It has no effect on abstract ordering of the fields, which is always from the most significant bit down.
For example, the `packed` format above specifies a 16-bit integer with three bit fields.

```text
| prefix (3 bits) |      value (10 bits)      | suffix (3 bits) |
```
In big-endian order, the first byte is the most significant, so the fields are encoded as follows:

```text
|b00|b01|b02|b03|b04|b05|b06|b07|b08|b09|b10|b11|b12|b13|b14|b15|
 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
|   prefix  |                 value                 |   suffix  |
```

In little-endian order, the first byte is the least significant, so the fields are encoded as follows:

```text
|b00|b01|b02|b03|b04|b05|b06|b07|b08|b09|b10|b11|b12|b13|b14|b15|
 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
|    value (low 5)  |  suffix   |   prefix  |   value (high 5)  |
```


## Constraints and enums

Bit-sized integers use the ordinary refinement syntax, with the same two-way
enforcement described in [Refinements](refinements.md). Enum suffixes may select
an exact bit width:

```vest
payload_kind = enum {
    Raw = 0u3,
    Words = 1u3,
    ...
}

header = bits {
    @kind: payload_kind,
    @count: u5 | 1..31,
    @length: u8,
}

packet = {
    @header: header,
    body: choose(@header.kind) {
        Raw => [u8; @header.length],
        Words => [u16; @header.count],
        _ => [u8; @header.length],
    },
}
```

Only unsigned integers and enums with unsigned bit-sized integer types are
allowed as bit fields. Dependency fields and dotted access work exactly as in
ordinary structures: `@kind` is unpacked while parsing the integer and is then
in scope for later fields, and preparation enforces it as a constraint in the
other direction.
