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
        Nil => Nothing,
        Cons => {
            head: u8,
            tail: list,
        },
    },
}
```

The compiler finds strongly connected components (SCCs), so mutually recursive
definitions are supported too. It emits owned `Box` links where Rust needs indirection in the value type.

**Parsing.** Recurses as the input demands, up to a fixed depth bound statically picked by the format. Exceeding the bound is a parse error.

**Preparation and serialization.** Preparation walks the value to the same
bound, summing lengths, and fails if the value nests deeper than the format
allows. Serialization traverses the value and writes the bytes in order.

## Note

Though `vest_lib` defines a bounded fixpoint format combinator that can express arbitrary recursion, the compilation of
recursive formats in Vest DSL is experimental: the implementation is incomplete and there is some engineering work remaining for a more robust support.
