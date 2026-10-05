# Benchmark corpora

- [`tls/`](tls/) contains TLS 1.3 handshake messages and records captured from
  public servers and Chrome for the `tls` benchmark, with the script that
  captured them.
- [`bitcoin/`](bitcoin/) contains four consecutive Bitcoin mainnet blocks for
  the `bitcoin` benchmark.
- [`cms/`](cms/) contains the common CMS `SignedData` corpus used by the
  `cms` benchmark. [`cms/ATTRIBUTION.md`](cms/ATTRIBUTION.md) records its NIST
  PKITS, European Commission DSS CAdES, and RFC 4134 sources and selection.
- [`cbor/cose-wg/`](cbor/cose-wg/) contains the IETF COSE Working Group vectors
  used by the `cbor` benchmark. Its attribution and public-domain dedication
  are stored beside the vectors.

Each directory's README describes its provenance and how the corpus is
validated.
