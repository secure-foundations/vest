# Recursion

Named formats may refer to themselves directly or through other definitions:

```vest
list_kind = enum {
    Nil = 0,
    Cons = 1,
}

list = {
    @kind: list_kind,
    value: choose(@kind) {
        Nil => [u8; 0],
        Cons => {
            head: u8,
            tail: list,
        },
    },
}
```

The compiler finds strongly connected components, so mutually recursive
definitions are supported too. It emits bounded fixpoint formats for the specification and owned `Box`
links where Rust needs indirection in the value type.

**Parsing.** Recurses as the input demands, up to a fixed depth bound statically picked by the format. Exceeding the bounde is a parse error.

**Preparation and serialization.** Preparation walks the value to the same
bound, summing lengths, and fails if the value nests deeper than the format
allows. Serialization traverses the value and writes the bytes in order.

## Note

Recursive generation is experimental: the implementation is incomplete and there is some engineering work remaining for a more robust support.
