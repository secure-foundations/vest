# `vest_lib`

`vest_lib` is Vest's parser and serializer combinator library verified in
[Verus](https://github.com/verus-lang/verus). It provides formal format
specifications, executable Rust implementations, and compositional correctness
and security proofs.

Use this crate directly when implementing a reusable format combinator or a complex format
primitive. Most formats can be expressed more concisely using
[Vest DSL](https://secure-foundations.github.io/vest/guide/getting-started.html) or
the [ASN.1 frontend](https://secure-foundations.github.io/vest/guide/asn1/).

The default feature is `std`. For smaller environments, select `alloc` alone or
disable default features for the `core`-only library:

```toml
[dependencies]
vest_lib = { version = "0.2", default-features = false, features = ["alloc"] }
```

Use the Verus and `vstd` versions pinned by the corresponding Vest release.
