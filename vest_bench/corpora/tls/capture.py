#!/usr/bin/env python3
"""Capture real TLS 1.3 handshakes for the `tls` benchmark.

The corpus has three sources:

* OpenSSL, through Python's `ssl` module, handshaking with public servers.
  OpenSSL's message callback reports every handshake message after
  decryption, and the raw record streams are kept as sent and received. Each
  server is contacted with OpenSSL's default groups (a hybrid ML-KEM share
  plus X25519), with each classic curve alone, and once more to resume the
  first session with a ticket.
* `openssl s_client`, offering a key share only for a group the server does
  not accept, which makes the server answer with a HelloRetryRequest, and
  separately requesting a stapled OCSP response and SCTs.
* Headless Google Chrome connecting to a local listener that records its first
  record and hangs up, for a browser's ClientHello: GREASE, a GREASE
  encrypted_client_hello, and extensions OpenSSL does not send.

Only TLS handshake messages and records are stored. Application data stays
encrypted, and no key material leaves this process. Resumption tickets are
opaque to anyone without the connection's resumption secret, which is never
recorded.

Output, both tab-separated with base64 payloads:

  handshakes.tsv  peer, client, sender, message type, Handshake message
  records.tsv     peer, client, sender, TLSPlaintext or TLSCiphertext record

Usage: capture.py [--chrome PATH] [--out DIR]
"""

from __future__ import annotations

import argparse
import base64
import re
import socket
import ssl
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

# Public servers run by different organizations on different TLS stacks.
HOSTS = [
    "www.google.com",
    "www.youtube.com",
    "www.cloudflare.com",
    "www.facebook.com",
    "www.amazon.com",
    "www.microsoft.com",
    "www.apple.com",
    "github.com",
    "www.wikipedia.org",
    "www.mozilla.org",
    "letsencrypt.org",
    "www.rust-lang.org",
    "www.fastly.com",
    "www.ietf.org",
    "www.netflix.com",
    "www.bing.com",
]

# OpenSSL names for each classic group; unsupported ones are skipped per host.
SINGLE_GROUPS = ["prime256v1", "secp384r1", "secp521r1", "X25519", "X448", "ffdhe2048"]

# Offered first, with the only key share, to provoke a HelloRetryRequest.
HRR_GROUPS = ["ffdhe2048:X25519", "secp521r1:X25519"]

HANDSHAKE_TYPES = {
    1: "client_hello",
    2: "server_hello",
    4: "new_session_ticket",
    5: "end_of_early_data",
    8: "encrypted_extensions",
    11: "certificate",
    13: "certificate_request",
    15: "certificate_verify",
    20: "finished",
    24: "key_update",
}

TIMEOUT = 10.0
POST_HANDSHAKE_IDLE = 1.5


@dataclass
class Capture:
    handshakes: list[tuple[str, str, str, bytes]] = field(default_factory=list)
    records: list[tuple[str, str, str, bytes]] = field(default_factory=list)

    def add_handshake(self, peer: str, client: str, sender: str, message: bytes) -> None:
        self.handshakes.append((peer, client, sender, message))

    def add_stream(self, peer: str, client: str, sender: str, stream: bytes) -> None:
        for record in split_records(stream):
            self.records.append((peer, client, sender, record))


def split_records(stream: bytes) -> list[bytes]:
    records, offset = [], 0
    while offset + 5 <= len(stream):
        end = offset + 5 + int.from_bytes(stream[offset + 3 : offset + 5], "big")
        if end > len(stream):
            break  # the peer closed mid-record
        records.append(stream[offset:end])
        offset = end
    return records


def message_name(message: bytes) -> str:
    if message[0] == 2 and message[6:38] == HRR_RANDOM:
        return "hello_retry_request"
    return HANDSHAKE_TYPES.get(message[0], f"type_{message[0]}")


# RFC 9846 Section 4.2.3: SHA-256("HelloRetryRequest").
HRR_RANDOM = bytes.fromhex(
    "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c"
)


class Session:
    """One TLS 1.3 connection driven through memory BIOs."""

    def __init__(self, host: str, context: ssl.SSLContext, session=None):
        self.host = host
        self.messages: list[tuple[str, bytes]] = []
        context._msg_callback = self._on_message
        self.incoming, self.outgoing = ssl.MemoryBIO(), ssl.MemoryBIO()
        self.tls = context.wrap_bio(
            self.incoming, self.outgoing, server_hostname=host, session=session
        )
        self.sent, self.received = bytearray(), bytearray()
        self.sock = socket.create_connection((host, 443), timeout=TIMEOUT)

    def _on_message(self, _conn, direction, _version, content_type, _msg_type, data):
        if content_type == 22:  # handshake, reported after decryption
            self.messages.append(("client" if direction == "write" else "server", bytes(data)))

    def _flush(self) -> None:
        data = self.outgoing.read()
        if data:
            self.sock.sendall(data)
            self.sent += data

    def _receive(self) -> bool:
        data = self.sock.recv(65536)
        if data:
            self.received += data
            self.incoming.write(data)
        return bool(data)

    def run(self) -> None:
        while True:
            try:
                self.tls.do_handshake()
                break
            except ssl.SSLWantReadError:
                self._flush()
                if not self._receive():
                    raise ConnectionError("server closed during the handshake")
        self._flush()
        if self.tls.version() != "TLSv1.3":
            raise ssl.SSLError(f"negotiated {self.tls.version()}")
        # Ask for a response so that servers which wait for application data
        # still send their NewSessionTickets.
        self.tls.write(
            f"HEAD / HTTP/1.1\r\nHost: {self.host}\r\nConnection: close\r\n\r\n".encode()
        )
        self._flush()
        self.sock.settimeout(POST_HANDSHAKE_IDLE)
        try:
            while self._receive():
                try:
                    while self.tls.read(65536):
                        pass
                except (ssl.SSLWantReadError, ssl.SSLZeroReturnError):
                    pass
        except (TimeoutError, socket.timeout, ssl.SSLError, ConnectionError):
            pass
        finally:
            self.sock.close()

    def store(self, capture: Capture, client: str) -> None:
        for sender, message in self.messages:
            capture.add_handshake(self.host, client, sender, message)
        capture.add_stream(self.host, client, "client", bytes(self.sent))
        capture.add_stream(self.host, client, "server", bytes(self.received))


def context(group: str | None = None) -> ssl.SSLContext:
    ctx = ssl.create_default_context()
    ctx.minimum_version = ssl.TLSVersion.TLSv1_3
    ctx.set_alpn_protocols(["http/1.1"])
    if group is not None:
        ctx.set_ecdh_curve(group)
    return ctx


def capture_openssl(capture: Capture, host: str, openssl: str) -> None:
    try:
        first = Session(host, context())
        first.run()
    except (OSError, ssl.SSLError) as error:
        print(f"  {host}: skipped ({error})", file=sys.stderr)
        return
    first.store(capture, f"{openssl}/default")
    print(f"  {host}: default, {len(first.messages)} messages", file=sys.stderr)

    session = first.tls.session
    if session is not None and session.has_ticket:
        resumed = Session(host, first.tls.context, session=session)
        try:
            resumed.run()
            resumed.store(capture, f"{openssl}/resumption")
            print(f"  {host}: resumption", file=sys.stderr)
        except (OSError, ssl.SSLError) as error:
            print(f"  {host}: resumption skipped ({error})", file=sys.stderr)

    for group in SINGLE_GROUPS:
        attempt = Session(host, context(group))
        try:
            attempt.run()
        except (OSError, ssl.SSLError):
            continue  # the server does not accept this group
        attempt.store(capture, f"{openssl}/{group}")
        print(f"  {host}: {group}", file=sys.stderr)


MSG_HEADER = re.compile(r"^(>>>|<<<) TLS [0-9.]+, Handshake \[length [0-9a-f]+\]")


def s_client(host: str, *args: str) -> list[tuple[str, bytes]]:
    """The handshake messages of one `openssl s_client` connection."""
    with tempfile.NamedTemporaryFile("r", suffix=".txt") as msgfile:
        try:
            subprocess.run(
                ["openssl", "s_client", "-connect", f"{host}:443", "-servername", host,
                 "-tls1_3", "-alpn", "http/1.1", *args, "-msg", "-msgfile", msgfile.name],
                stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL, timeout=TIMEOUT * 2, check=False,
            )
        except subprocess.TimeoutExpired:
            return []
        return parse_msgfile(Path(msgfile.name).read_text())


_CT_LOG_LIST: Path | None = None


def ct_log_list() -> Path:
    """A log list naming one throwaway key. `s_client -ct` refuses to run
    without a list; the SCTs are recorded, not validated."""
    global _CT_LOG_LIST
    if _CT_LOG_LIST is None:
        key = subprocess.run(["openssl", "genpkey", "-algorithm", "EC",
                              "-pkeyopt", "ec_paramgen_curve:P-256"],
                             capture_output=True, check=True).stdout
        public = subprocess.run(["openssl", "pkey", "-pubout", "-outform", "DER"],
                                input=key, capture_output=True, check=True).stdout
        path = Path(tempfile.mkstemp(suffix=".cnf")[1])
        path.write_text("enabled_logs = placeholder\n\n[placeholder]\n"
                        "description = placeholder\n"
                        f"key = {base64.b64encode(public).decode()}\n")
        _CT_LOG_LIST = path
    return _CT_LOG_LIST


def capture_s_client(capture: Capture, host: str, openssl: str) -> None:
    for groups in HRR_GROUPS:
        messages = s_client(host, "-groups", groups)
        if any(message_name(m) == "hello_retry_request" for _, m in messages):
            for sender, message in messages:
                capture.add_handshake(host, f"{openssl}/hrr-{groups}", sender, message)
            print(f"  {host}: HelloRetryRequest with {groups}", file=sys.stderr)
            break
    # Request a stapled OCSP response and SCTs, which servers return as
    # extensions of their Certificate message's first entry.
    messages = s_client(host, "-status", "-ct", "-ctlogfile", str(ct_log_list()))
    if any(message_name(m) == "certificate" for _, m in messages):
        for sender, message in messages:
            capture.add_handshake(host, f"{openssl}/status-ct", sender, message)
        print(f"  {host}: status_request and signed_certificate_timestamp", file=sys.stderr)


def parse_msgfile(text: str) -> list[tuple[str, bytes]]:
    messages, current = [], None
    for line in text.splitlines():
        header = MSG_HEADER.match(line)
        if header:
            current = ("client" if header.group(1) == ">>>" else "server", bytearray())
            messages.append(current)
        elif line.startswith("    ") and current is not None:
            current[1].extend(bytes.fromhex(line))
        else:
            current = None
    return [(sender, bytes(data)) for sender, data in messages]


def first_record(connection: socket.socket) -> bytes | None:
    connection.settimeout(TIMEOUT)
    data = bytearray()
    try:
        while len(data) < 5 or len(data) < 5 + int.from_bytes(data[3:5], "big"):
            chunk = connection.recv(65536)
            if not chunk:
                break
            data += chunk
    except (TimeoutError, socket.timeout):
        pass
    records = split_records(bytes(data))
    return records[0] if records else None


def capture_chrome(capture: Capture, chrome: str, count: int) -> None:
    version = subprocess.run([chrome, "--version"], capture_output=True, text=True,
                             check=True).stdout.split()[-1]
    client = f"chrome-{version}"
    for _ in range(count):
        # A fresh browser process, profile, and listener per ClientHello:
        # Chrome permutes its extension order per process, and opens parallel
        # connections that must not leak into the next capture.
        with socket.socket() as listener, tempfile.TemporaryDirectory() as profile:
            listener.bind(("127.0.0.1", 0))
            listener.listen(8)
            listener.settimeout(TIMEOUT * 3)
            port = listener.getsockname()[1]
            browser = subprocess.Popen(
                [chrome, "--headless=new", "--no-first-run", "--no-default-browser-check",
                 "--disable-gpu", f"--user-data-dir={profile}", f"https://localhost:{port}/"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            record = None
            try:
                while record is None:
                    connection, _ = listener.accept()
                    with connection:
                        record = first_record(connection)
            except (TimeoutError, socket.timeout):
                pass
            finally:
                browser.kill()
                browser.wait()
        # The ClientHello must arrive whole in the first record.
        if (record is None or record[0] != 22 or record[5] != 1
                or len(record) != 9 + int.from_bytes(record[6:9], "big")):
            print("  chrome: no complete ClientHello received", file=sys.stderr)
            continue
        capture.records.append(("localhost", client, "client", record))
        capture.add_handshake("localhost", client, "client", record[5:])
        print(f"  chrome: ClientHello of {len(record) - 5} bytes", file=sys.stderr)


def write(capture: Capture, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    with (out / "handshakes.tsv").open("w") as f:
        f.write("# peer\tclient\tsender\tmessage\tbase64(Handshake)\n")
        for peer, client, sender, message in capture.handshakes:
            encoded = base64.b64encode(message).decode()
            f.write(f"{peer}\t{client}\t{sender}\t{message_name(message)}\t{encoded}\n")
    with (out / "records.tsv").open("w") as f:
        f.write("# peer\tclient\tsender\tbase64(record)\n")
        for peer, client, sender, record in capture.records:
            f.write(f"{peer}\t{client}\t{sender}\t{base64.b64encode(record).decode()}\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--chrome", default="/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
    parser.add_argument("--chrome-hellos", type=int, default=4)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    openssl = "openssl-" + ssl.OPENSSL_VERSION.split()[1]
    capture = Capture()
    for host in HOSTS:
        capture_openssl(capture, host, openssl)
        capture_s_client(capture, host, openssl)
    if Path(args.chrome).exists():
        capture_chrome(capture, args.chrome, args.chrome_hellos)
    write(capture, args.out)
    print(f"{len(capture.handshakes)} handshake messages, {len(capture.records)} records",
          file=sys.stderr)


if __name__ == "__main__":
    main()
