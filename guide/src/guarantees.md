# What Vest proves

Binary parsers and serializers are a classic source of security vulnerabilities, due to the conflicting goals of high performance and adherence to complex binary formats.
The most common implementation mistakes are:
- Memory safety issues, such as [use-after-free](https://cwe.mitre.org/data/definitions/416.html), [double-free](https://cwe.mitre.org/data/definitions/415.html), and [out-of-bounds accesses](https://cwe.mitre.org/data/definitions/125.html)
- Arithmetic issues, such as [integer overflow](https://cwe.mitre.org/data/definitions/190.html) and [underflow](https://cwe.mitre.org/data/definitions/191.html)
- [Improper Input Validation](https://cwe.mitre.org/data/definitions/20.html)
- [Deserialization of Untrusted Data](https://cwe.mitre.org/data/definitions/502.html)
- [Uncontrolled Resource Consumption](https://cwe.mitre.org/data/definitions/400.html)
- [Uncontrolled Recursion](https://cwe.mitre.org/data/definitions/674.html)

There are also more subtle issues that root in the format itself, such as:
- **Format confusion.** It occurs when objects from different semantic domains, or distinct objects from the same semantic domain are encoded with the same byte representation. In this case, a parser fundamentally cannot distinguish between the two objects, making it vulnerable to cross-protocol attacks.
- **Format malleability.** It occurs when a single object can be encoded in multiple ways, and a parser accepts all of them. In this case, a parser can be tricked into accepting a modified input that is semantically equivalent to the original, but would yield completely different hash values or signatures. This is a common source of signature forgery or transaction malleability attacks.

Vest's answer is to formally prove the absence of these vulnerabilities,
for each format you define, without asking you to write proofs.

This page describes what you get, in plain terms, and then maps each guarantee
onto the interface that carries it in `vest_lib`.

## Safety, for every format

These hold for every format Vest generates.

- **Memory safety.** Parsers and serializers are written in safe Rust, so Rust's ownership
  and borrowing rules rule out use-after-free and double-free. Verus adds proofs
  that there are no out-of-bounds accesses.
- **Arithmetic safety.** No integer overflow or underflow, including in length/offset
  calculations — the classic place where a hand-written parser goes wrong.
- **Termination and panic freedom.** Parsing and serializing terminate and never
  panic, on *any* input.

## Correctness and security

These are the properties that prevent format confusion and malleability. Not every format can satisfy all of them, and Vest is explicit
about which ones a given format actually establishes.

- **Parser soundness.** If parsing succeeds, the result is a valid instance of
  the format, and the number of bytes consumed is exactly the formally specified wire length of that instance.
- **Parser completeness.** Every valid instance of the format can be successfully parsed from its byte representation.
- **Parser non-malleability.** Each value has a *unique* byte representation accepted by the parser.
  Modifying or truncating an accepted input changes the outcome — it fails, or
  yields a different value.
- **Parser non-extensibility.** Appending bytes to an accepted input does not
  change what was already parsed.
- **Parser productivity.** A successful parse consumes at least one byte, making "progress" on the input.
- **Serializer non-ambiguity.** Two distinct valid values never serialize to the
  same bytes.
- **Round trips.** Together, for unambiguous, non-malleable formats, parsing and serializing are mutual inverses: parse-then-serialize reproduces the consumed
  bytes, and serialize-then-parse recovers the value.

## When a format cannot be non-malleable

While non-malleability is the gold standard in cryptographic systems, it
violates [Postel’s law](https://en.wikipedia.org/wiki/Robustness_principle): *be conservative in what you do; be liberal in what you accept*.
Many foundational security standards explicitly rely on malleability for backwards-compatibility, extensibility, and interoperability.
Concise Binary Object Representation (CBOR) permits multiple valid encodings and
separately defines deterministic serialization as required; Cryptographic
Message Syntax (CMS) permits the malleable Basic Encoding Rules (BER) for many
structures and requires Distinguished Encoding Rules (DER) only at particular
authenticated boundaries; and Internet Key Exchange (IKE) allows flexible
ordering of payloads and defines explicit rules for ignoring payloads to
preserve forward compatibility.

In Vest, malleable formats are explicitly marked (those that do not carry the `NonMalleable` proof trait or only carry it conditionally), so you cannot accidentally rely on uniqueness that is not there.
The practical consequence is that if your application needs byte-faithful round trips — verifying a signature over the bytes you parsed, for instance — add `NonMalleable` as a requirement (trait bound) to your format.

The DSL currently only accepts and produces non-malleable formats, and we are working on bringing malleable features into the DSL securely.


## Vest's TCB

The guarantees above rest on a trusted computing base:

- **`rustc`**, the Rust compiler;
- **Verus** and the **Z3** solver;
- **`vstd`**, Verus's trusted standard-library specification;
- top-level theorem statements in **`vest_lib`**.

> Vest also says nothing about whether your format is the *right* format. That it
parses/serializes safely and securely does not mean it matches the RFC you are
reading. For now, we recommend testing your format against real-world corpora. In the future, we hope to provide an automated testing framework that checks a format against its RFC or other authoritative specification, and flags any discrepancies.
