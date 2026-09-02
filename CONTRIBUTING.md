# Vest Contributing Guide

Thanks for your interest in Vest! Vest is an open-source research project and
we welcome contributions: bug reports, documentation fixes, new formats, new combinators, and DSL or ASN.1 compiler feature requests are all very useful.

## Reporting an issue

There are several components in Vest. If you are confident that the error you are seeing is a bug in one of Vest's components, please open an issue on GitHub.
Depending on
where it went wrong, please include:

- **Vest DSL or ASN.1 compiler bug**: the `.vest` or `.asn1` source (reduced
  as far as you can), the exact command you ran, and the full output.
- **Generated code that does not compile**: the schema plus the `rustc` error.
- **Generated code that does not verify**: the schema plus the Verus output. Running with `--expand-errors` usually points at
  the specific proof obligation that could not be discharged.
- **`vest_lib` issue**: a small reproducer, plus which feature configuration
  you were using (`std`, `alloc`, or `core`-only).

Please also mention your platform and whether you are using the pinned Verus
release from `verus.json`, since verification behaviour can differ across Verus
versions.

## Getting set up

You only need a stable Rust toolchain to build the compilers and to compile and
run generated code.

For example, to build the Vest DSL compiler:

```console
git clone https://github.com/secure-foundations/vest.git
cd vest
cargo build --release -p vest
```

Verus is needed for verification.
We recommend installing the pinned Verus release:

```console
./scripts/install-verus.sh
export PATH="$PWD/.verus:$PATH"
```

`verus.json` records the
Verus version, its upstream commit, the Rust version, and a SHA-256 digest for
each platform archive. `scripts/install-verus.sh` checks the digest before
unpacking anything, and is safe to re-run. It exits early when the right
version is already installed.

### Vest repository layout

| Path               | What it is                                                         |
| ------------------ | ------------------------------------------------------------------ |
| `vest/`            | the `.vest` DSL compiler (published to crates.io)                  |
| `vest_lib/`        | the verified combinator library (published to crates.io)           |
| `vest_asn1/`       | the ASN.1 frontend (not published to crates.io yet)                |
| `vest_tests/`      | `.vest` files and their generated Rust                             |
| `vest_asn1_tests/` | ASN.1 modules and their generated Rust                             |
| `vest_dev/`        | dev examples of handwritten combinator formats and some benchmarks |
| `guide/`           | the mdBook guide, plus tests that compile its snippets             |
| `dev_docs/`        | internal design notes                                              |

### Contributions written with AI assistance

AI assistance is welcome, and this repository already contains work produced
with the help of it. We do ask a couple of things: 1. _Please disclose it in the pull request._ 2. _Please understand what you are submitting._

## Formatting

- `vest` and `vest_asn1` are ordinary Rust and are checked with `rustfmt`:
  `cargo fmt -p vest -p vest_asn1 -- --check`.
- Generated code under `vest_tests/src/` are formatted with a pinned
  `verusfmt`, driven by the Makefile. A few of the largest files are
  deliberately left unformatted because `verusfmt` stalls on them; the exclusion
  list is in `vest_tests/Makefile`.
- `vest_lib` is not auto-formatted. Please match the
  surrounding style.

## Running the checks

Basic checks for formatting, linting, and tests:

```console
cargo fmt -p vest -p vest_asn1 -- --check
cargo clippy -p vest -p vest_asn1 --all-targets --locked
cargo test --workspace --locked
```

Regenerate code and the guide when the corresponding sources change:

```console
make -C vest_tests vest          # regenerate everything from the .vest files
make -C vest_tests bad           # confirm the bad corpus is rejected
make -C vest_asn1_tests generate # regenerate everything from the .asn1 files
cargo test -p vest_guide_tests --locked
scripts/build-guide.sh && mdbook test
git status --porcelain           # review and commit the intended outputs
```

After committing those outputs, rerunning the generators should produce no diff
and no new untracked files; CI enforces this from a clean checkout.

Verification, once Verus is on your `PATH`:

```console
cargo verus verify -p vest_lib --locked --check-toolchain -- --expand-errors
cargo verus verify -p vest_lib --no-default-features --locked --check-toolchain -- --expand-errors
cargo verus verify -p vest_lib --no-default-features --features alloc --locked --check-toolchain -- --expand-errors
cargo verus verify -p vest_tests --locked --check-toolchain -- --expand-errors
cargo verus verify -p vest_dev --locked --check-toolchain -- --expand-errors
cargo verus verify -p vest_asn1_tests --locked --check-toolchain -- --expand-errors --rlimit 100
```

## Adding a test `.vest` or `.asn1` file

For the DSL, put the schema in `vest_tests/src/`, then add it to `VEST_FILES` in
`vest_tests/Makefile`, declare the generated module in `vest_tests/src/lib.rs`,
and add the generated `.rs` to `VERUSFMT_FILES` unless it is large enough to
stall the formatter.
Run `make -C vest_tests vest` and commit the result.

A schema that _should_ be rejected goes in `vest_tests/bad/` instead. `make -C vest_tests bad`
checks that every one of them fails.

ASN.1 works the same way: add the `.asn1` module, add a generation rule
to `vest_asn1_tests/Makefile`, and declare the module in
`vest_asn1_tests/src/lib.rs`.

## Working on `vest_lib`

We recommend reading the [library documentation](https://secure-foundations.github.io/vest/vest_lib/) before making changes.
The trait system in `vest_lib` is quite subtle, and how each combinator (and its proof) composes with others is not always obvious.
Feel free to ask questions in GitHub Issues or the Verus Zulip if you are unsure about the design or how to implement a new combinator/format.

## For maintainers

**Upgrading Verus.** Update `verus.json` and the exact `vstd` version in the
workspace `Cargo.toml` together.
`verus.json` needs the new version, commit, Rust version, and the SHA-256
of all three platform archives. Then run the full verification matrix, since
Verus upgrades can change proof results and performance.

**Releasing.** Publish only from `main`, and tag with the exact manifest
version: `vest_lib-vVERSION` or `vest-vVERSION`. The release workflow refuses a
tag that disagrees with the manifest, and refuses to publish a commit that is
not on the default branch. Publish `vest_lib` **before** `vest` and wait for the
index to update: Cargo will not enforce this for you, because `vest` does not
depend on `vest_lib`, but code generated by `vest` does. Refresh
`docs/vest_lib/` before tagging.

---

Vest is licensed under the MIT license, and contributions are accepted under the same terms.

Thanks again for helping out.
