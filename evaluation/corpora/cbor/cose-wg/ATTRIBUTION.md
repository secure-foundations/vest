# COSE Working Group corpus

This directory is a curated copy of the `sign-tests`, `sign1-tests`,
`encrypted-tests`, `mac-tests`, and `mac0-tests` directories from the IETF COSE
Working Group's `cose-wg/Examples` repository at commit
`53c9d634333bb4f529d78f5980fffa2667ee2c12`.

Each JSON document contains a complete encoded COSE protocol message in
`output.cbor`, along with its diagnostic form and cryptographic inputs or
intermediate values. The repository is the example/test-vector source cited by
the COSE specification and releases the files into the public domain. Its
license is retained as `LICENSE`.

This is real protocol-shaped CBOR from an official interoperability corpus, not
production traffic. We use all well-formed `output.cbor` values accepted by the
four measured generic CBOR implementations; cryptographic verification is
outside the timed operation.
