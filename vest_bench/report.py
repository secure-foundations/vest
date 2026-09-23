#!/usr/bin/env python3
"""Print the Vest-vs-hand comparison collected by `make bench`.

Reads the criterion estimates under ../target/criterion and prints one row per
format and operation. `ratio` below 1.00 means the generated code is faster than
the hand-written baseline.
"""

import json
import os
import sys

FORMATS = [
    ("flat", "flat struct, fixed + length-prefixed fields"),
    ("table", "[entry; @count], counted repetition"),
    ("nest", "eight header/footer layers around a payload"),
    ("tlv", "[u8; @len] >>= choose(@tag), tagged union"),
    ("varint", "btc_varint count and lengths"),
    ("bits", "bit-packed header plus byte-aligned body"),
    ("bounded_list", "[u8; @len] >>= Vec<item>"),
    ("tail_list", "Tail >>= Vec<item>"),
]

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "target", "criterion")


def load():
    out = {}
    if not os.path.isdir(ROOT):
        return out
    for dirpath, _, files in os.walk(ROOT):
        if dirpath.endswith(os.sep + "new") and "estimates.json" in files:
            name = os.path.relpath(dirpath, ROOT)[: -len(os.sep + "new")]
            with open(os.path.join(dirpath, "estimates.json")) as f:
                out[name.replace(os.sep, "/")] = json.load(f)["mean"]["point_estimate"] / 1000.0
    return out


def main():
    r = load()
    if not r:
        sys.exit("no criterion results found; run `make bench` first")
    # Optional format filter, so a subset run does not print stale rows from an
    # earlier full run.
    wanted = set(sys.argv[1:])
    formats = [f for f in FORMATS if not wanted or f[0] in wanted]
    for op in ("parse", "serialize"):
        print(f"\n--- {op} (microseconds per pass; lower is better) ---")
        print(f"{'format':<15}{'vest':>9}{'hand':>9}{'ratio':>9}   what it isolates")
        for name, desc in formats:
            kv, kh = f"{name}_{op}/vest", f"{name}_{op}/hand"
            if kv in r and kh in r:
                print(f"{name:<15}{r[kv]:9.1f}{r[kh]:9.1f}{r[kv] / r[kh]:8.2f}x   {desc}")
    print()


if __name__ == "__main__":
    main()
