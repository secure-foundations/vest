# ASN.1 frontend

`src/frontend/ast.rs` and `src/frontend/parser.rs` are adapted from
[Synta](https://codeberg.org/abbra/synta)'s `synta-codegen` crate. The previously
vendored manifest recorded version 0.3.0; that locally patched copy is preserved
in Vest's history at commit `ce6705fad1af476e828feae6621d0bcf4d0c1665`.

Vest maintains these files locally to retain constraints and typed values and
to reject unsupported syntax instead of silently changing a schema's meaning.
They do not depend on Synta's Rust or C code generators.

Synta's copyright notices and MIT/Apache-2.0 license texts are retained in
[`LICENSE-MIT-SYNTA`](LICENSE-MIT-SYNTA) and
[`LICENSE-APACHE-SYNTA`](LICENSE-APACHE-SYNTA).
