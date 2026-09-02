# `vest`

`vest` is the compiler for the [Vest DSL](https://secure-foundations.github.io/vest/guide/dsl/reference.html). It translates concise binary-format descriptions into efficient Rust parsers and serializers (composed of [`vest_lib`](https://crates.io/crates/vest_lib) combinators) whose correctness and security properties are verified by [Verus](https://github.com/verus-lang/verus).

See the [Vest guide](https://secure-foundations.github.io/vest/guide/) for installation, language documentation, and generated APIs. The compiler itself is not verified; Verus verifies the generated code.
