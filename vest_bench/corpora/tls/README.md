# TLS 1.3 corpus

Real TLS 1.3 handshakes, captured on 2026-09-24 (UTC) by
[`capture.py`](capture.py) with OpenSSL 3.6.3 (through Python 3.14's `ssl`
module and `openssl s_client`) and Google Chrome 153.0.8010.47.

## Contents

`handshakes.tsv` holds 909 complete `Handshake` messages (header included,
586,761 bytes in total). Messages after the ServerHello are recorded as
OpenSSL reported them after decryption.

| Message | Count |
| --- | ---: |
| ClientHello | 130 |
| ServerHello | 110 |
| HelloRetryRequest | 16 |
| EncryptedExtensions | 110 |
| Certificate | 96 |
| CertificateVerify | 96 |
| Finished | 220 |
| NewSessionTicket | 131 |

`records.tsv` holds the 969 records of the OpenSSL connections and Chrome's
ClientHello records, exactly as sent on the wire: `TLSPlaintext` records up to
the ChangeCipherSpec, and `TLSCiphertext` records after it.

Both files are tab-separated, with a header line starting with `#`. The
columns are the server, the client configuration, the sender (`client` or
`server`), for handshakes the message type, and the base64-encoded bytes.

## Sources

The servers are www.google.com, www.youtube.com, www.cloudflare.com,
www.facebook.com, www.amazon.com, www.microsoft.com, www.apple.com,
github.com, www.wikipedia.org, www.mozilla.org, letsencrypt.org,
www.rust-lang.org, www.fastly.com, www.ietf.org, www.netflix.com, and
www.bing.com. They cover several independent TLS stacks. Each server was
contacted:

- with OpenSSL's default groups, which offer X25519MLKEM768 and X25519 key
  shares (`openssl-3.6.3/default`);
- again, resuming that session with a ticket, which adds `pre_shared_key` to
  both hellos (`resumption`);
- once for each of P-256, P-384, P-521, X25519, X448, and ffdhe2048 alone,
  keeping the groups the server accepted (`prime256v1`, …);
- with `s_client` offering a key share only for ffdhe2048, which servers
  answer with a HelloRetryRequest (`hrr-ffdhe2048:X25519`);
- with `s_client -status -ct`, requesting a stapled OCSP response and SCTs
  (`status-ct`).

The four Chrome ClientHellos (`localhost`, `chrome-153.0.8010.47`) come from
fresh headless Chrome processes connecting to a local listener. They carry
GREASE values, a GREASE `encrypted_client_hello`, `application_settings`, and
a permuted extension order.

## What is not in the corpus

Application data stays encrypted, and no key material was exported, so none
of the ciphertext records can be decrypted. The resumption tickets and PSK
binders are opaque without the connections' resumption secrets, which were
never recorded. The OpenSSL connections sent only `HEAD /`, so that servers
waiting for application data would still issue their NewSessionTickets.

No CertificateRequest, EndOfEarlyData, or KeyUpdate message appears: none of
these servers asked for a client certificate, and no connection sent early
data or updated its keys.

## Validation

`cargo test -p vest_bench --test real_corpora` checks that each message and
record is accepted by the Vest specification in
[`vest_tests/src/tls.vest`](../../../vest_tests/src/tls.vest), consumes all of
its bytes, and re-serializes to the same bytes. The test also checks that the
corpus reaches the specification's precise extension bodies, such as each
named group's key-share encoding, the ECH outer ClientHello, and the stapled
OCSP response, and not only its fallback `Tail` arms. The `tls` benchmark
additionally requires Rustls 0.22 to parse and re-encode every message
exactly.

Running `capture.py` again replaces both files with a fresh capture. Servers
change their configurations over time, so a new capture will differ.
