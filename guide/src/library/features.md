# Feature configurations

`vest_lib` supports three runtime environments:

| Cargo configuration | Available environment |
|---|---|
| default features | `std`, including all heap-backed formats; full error traces are off by default |
| `default-features = false, features = ["alloc"]` | `no_std` with `Vec`, `Box`, and `String` for heap-backed formats |
| `default-features = false` | `core`-only formats and caller-provided buffers |

```toml
[dependencies]
vest_lib = { version = "0.2", default-features = false, features = ["alloc"] }
```

`std` enables `alloc`. Without `alloc`, one can still use fixed-width formats, formats with raw byte fields, and serialization into caller-provided slices.
Heap-backed collection parsers, owned string values, `serialize_with_vec`, and the generic
CBOR codec require `alloc` (or `std`).

## Error traces

`ParseError` and `PreSerializeError` always retain the failure kind and, when
available, the innermost named format that reported it. This does not require
allocation.

Enable `error-trace` to also record a stack of enclosing named formats.

```toml
[dependencies]
vest_lib = { version = "0.2", features = ["error-trace"] }
```

This diagnostic feature is off by default, even with `std`. It enables `alloc`
but does not require `std`, so it also works with
`default-features = false, features = ["error-trace"]`. Errors may allocate and become heavier when propagating, so leave it disabled
for production builds.

## Verus compatibility

Vest and `vest_lib` must be used with the Verus and `vstd` versions this release
pins. The Verus version is in
[`verus.json`](https://github.com/secure-foundations/vest/blob/main/verus.json)
and the `vstd` version is in the workspace `Cargo.toml`.
