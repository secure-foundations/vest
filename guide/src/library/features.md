# Feature configurations

`vest_lib` has three supported configurations:

| Cargo configuration | Available environment |
|---|---|
| default features | `std`, including allocation-backed errors and formats |
| `default-features = false, features = ["alloc"]` | `no_std` with `Vec`, `Box`, and owned recursive values |
| `default-features = false` | `core`-only formats and caller-provided buffers |

```toml
[dependencies]
vest_lib = { version = "0.2", default-features = false, features = ["alloc"] }
```

The generic CBOR value codec and BER formats that flatten constructed strings
require allocation. Primitive combinators, in-place serialization, and the
non-owning parts of the ASN.1 backend remain available in smaller
configurations where their types permit it.

Vest and `vest_lib` must be used with the Verus and `vstd` versions recorded by
the release. The repository pins the complete compatible set.

