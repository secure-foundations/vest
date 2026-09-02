# Feature configurations

`vest_lib` has three supported configurations:

| Cargo configuration | Available environment |
|---|---|
| default features | `std`: everything available, including heap-backed formats and full error traces |
| `default-features = false, features = ["alloc"]` | `no_std` with `Vec`, `Box` and `String` for heap-backed formats and error reporting |
| `default-features = false` | `core`-only formats and caller-provided buffers |

```toml
[dependencies]
vest_lib = { version = "0.2", default-features = false, features = ["alloc"] }
```

Vest and `vest_lib` must be used with the Verus and `vstd` versions this release
pins. The Verus version is in
[`verus.json`](https://github.com/secure-foundations/vest/blob/main/verus.json)
and the `vstd` version is in the workspace `Cargo.toml`.
