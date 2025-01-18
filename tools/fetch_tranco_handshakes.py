import ssl
import sys
import time
import socket
import argparse
import threading


server_trace = b""
client_trace = b""
server_started = False


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def forward(src, dst, direction_label):
    """
    Read data from src, log it, and send to dst.
    """
    try:
        while True:
            data = src.recv(4096)
            if not data: break

            if direction_label.startswith("client"):
                global client_trace
                client_trace += data

            if direction_label.startswith("server"):
                global server_trace
                server_trace += data

            # print(f"[{direction_label}] {len(data)} byte(s)")
            dst.sendall(data)

    except Exception as e:
        eprint(f"[{direction_label}] error: {e}")

    finally:
        src.close()
        dst.close()


def run_proxy(host, port, target_host, target_port):
    global server_started

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.bind((host, port))
        sock.listen(5)
        # print(f"proxy listening on {host}:{port}")

        server_started = True

        # Handles one client and then exit
        client_conn, _ = sock.accept()

        try:
            target_conn = socket.create_connection((target_host, target_port), timeout=5)
            eprint(f"connected to {target_host}:{target_port}")

            t1 = threading.Thread(target=forward, args=(client_conn, target_conn, "client -> server"))
            t2 = threading.Thread(target=forward, args=(target_conn, client_conn, "server -> client"))
            t1.start()
            t2.start()
            t1.join()
            t2.join()
        except Exception as e:
            eprint(f"connection handling error: {e}")

        finally:
            client_conn.close()


def split_tls_records(data):
    """
    Split a sequence of data into TLS records
    """
    records = []

    while data:
        rec_type = data[0]
        version = data[1:3]
        record_length = int.from_bytes(data[3:5], "big")
        record = data[5:5+record_length]
        records.append((rec_type, version, record))
        data = data[5+record_length:]

    return records


def get_tls_handshake_data(args, domain):
    global server_trace
    global client_trace
    global server_started

    server_trace = b""
    client_trace = b""
    server_started = False

    # Start a server first
    server_thread = threading.Thread(target=run_proxy, args=(args.proxy_host, args.proxy_port, domain, 443))
    server_thread.start()

    try:
        while not server_started: time.sleep(0.01)

        sock = socket.create_connection((args.proxy_host, args.proxy_port), timeout=5)
        context = ssl.create_default_context()
        tls_socket = context.wrap_socket(sock, server_hostname=domain)

        tls_socket.do_handshake()

        request = f"GET / HTTP/1.1\r\nHost: {domain}\r\nConnection: close\r\n\r\n"
        tls_socket.send(request.encode())

        response = b""
        while True:
            data = tls_socket.recv(4096)
            if not data:
                break
            response += data

        # print(f"received {len(response)} byte(s) of TLS application data")

        tls_socket.close()

        eprint(f"[client -> server]: {len(client_trace)} byte(s)")
        eprint(f"[server -> client]: {len(server_trace)} byte(s)")

        client_sent_records = split_tls_records(client_trace)
        server_sent_records = split_tls_records(server_trace)

        # for i, record in enumerate(client_sent_records):
        #     print(f"client sent record {i} of type {record[0]}")

        # for i, record in enumerate(server_sent_records):
        #     print(f"server sent record {i} of type {record[0]}")

        # Only grab all handshake messages (and discard, e.g., change cipher spec, application data)
        client_handshakes = [record for record in client_sent_records if record[0] == 22]
        server_handshakes = [record for record in server_sent_records if record[0] == 22]

        eprint("client sent", len(client_handshakes), "TLS handshake message(s)")
        eprint("server sent", len(server_handshakes), "TLS handshake message(s)")
    finally:
        server_thread.join()

    return client_handshakes, server_handshakes


def bytes_to_rust_literal(data):
    return "&[" + ", ".join(hex(b) for b in data) + "]"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--proxy-host", default="localhost")
    parser.add_argument("--proxy-port", type=int, default=4321)
    # parser.add_argument("--target-port", type=int, default=443)
    parser.add_argument("list", help="List of domain names to connect to")
    parser.add_argument("--limit", type=int, help="Only take the first <limit> number of successful handshakes")
    args = parser.parse_args()

    num_suc = 0

    print("pub const HANDSHAKE_DATA: &[(&str, &[&[u8]], &[&[u8]])] = &[")

    with open(args.list) as f:
        for domain in f.readlines():
            if args.limit is not None and num_suc >= args.limit:
                break

            domain = domain.strip()
            eprint(f"### [{num_suc}/{args.limit}] connecting to {domain}")

            try:
                client, server = get_tls_handshake_data(args, domain)

                print(f"    (\"{domain}\", &[")
                for record in client:
                    print(f"        {bytes_to_rust_literal(record[2])},")

                print("    ], &[")
                for record in server:
                    print(f"        {bytes_to_rust_literal(record[2])},")

                print("    ]),")

                num_suc += 1
            except Exception as e:
                eprint(f"error: {e}")

        print("];")


if __name__ == "__main__":
    main()
