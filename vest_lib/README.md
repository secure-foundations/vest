# vest_lib

`vest_lib` is Vest's verified parser and serializer combinator library for
[Verus](https://github.com/verus-lang/verus). It provides pure format
specifications, executable Rust implementations, and compositional correctness
and security proofs.

Use this crate directly when implementing a reusable format or backend
primitive. Most application schemas are more concise in the
[Vest DSL](https://secure-foundations.github.io/vest/guide/getting-started.html) or
the [ASN.1 frontend](https://secure-foundations.github.io/vest/guide/asn1/).

The default feature is `std`. For smaller environments, select `alloc` alone or
disable default features for the `core`-only library:

```toml
[dependencies]
vest_lib = { version = "0.2", default-features = false, features = ["alloc"] }
```

Serializers write into caller-provided slices without allocating. The library
also includes modular ASN.1 DER/BER formats and a generic CBOR codec.

- [Combinator guide](https://secure-foundations.github.io/vest/guide/library/combinators.html)
- [Formal guarantees](https://secure-foundations.github.io/vest/guide/guarantees.html)
- [Verusdoc API reference](https://secure-foundations.github.io/vest/vest_lib/)
- [Project repository](https://github.com/secure-foundations/vest)

Use the Verus and `vstd` versions pinned by the corresponding Vest release.
