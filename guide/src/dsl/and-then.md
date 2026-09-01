# `>>=`

`left >>= right` means "take the region `left` describes, then parse `right` against it."

The value of the whole expression is `right`'s value.

**Parsing.** Extract a bounded region from the input defined by `left`, then parse `right` from that region.
`right` must consume the region *entirely* — leftover bytes
are an error.

**Preparation and serialization.** Preparation prepares `right` and requires its
length to equal the region `left` declares. Serialization writes
`right`'s bytes directly.

Currently, the left side must be `[u8; length]` or `Tail`. Using an integer or any other
format there is an error.

## Bounding `Vec` with a length field

```vest
item = { value: u16, }

list = {
    @byte_length: u16,
    values: [u8; @byte_length] >>= Vec<item>,
}
```

`Vec<item>` repeats until its region runs out. Because the region is exactly
`byte_length` bytes, the repetition stop. Preparation checks that the items really do add up to `byte_length`.

## Reinterpreting the remainder of a region

`Tail` names everything left in the enclosing region, which turns `>>=` into
"reinterpret the remainder":

```vest
item = { value: u16, }

items = Tail >>= Vec<item>
```

This is the idiom for a message that ends in a homogeneous run of records. It
also composes: inside a format already bounded by a length field, `Tail` means
the rest of *that* region, not the rest of the input buffer.
