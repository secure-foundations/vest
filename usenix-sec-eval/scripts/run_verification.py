#!/usr/bin/env python3
"""Run one cold-source Verus measurement and preserve all raw artifacts."""

from __future__ import annotations

import argparse
import json
import os
import platform
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser()
    parser.add_argument("label")
    parser.add_argument("crate", type=Path)
    parser.add_argument("--module")
    parser.add_argument("--threads", type=int, default=10)
    parser.add_argument("--profile", action="store_true")
    args = parser.parse_args()

    crate = args.crate.resolve()
    (crate / "src" / "lib.rs").touch()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = root / "results" / "raw" / "verification" / args.label / stamp
    out.mkdir(parents=True)

    verus_args = ["--time-expanded", "--output-json", "--num-threads", str(args.threads)]
    if args.module:
        verus_args += ["--verify-module", args.module]
    if args.profile:
        verus_args.append("--profile-all")
    command = [
        "cargo", "verus", "verify", "--fwd-verus-args-to", "roots", "--lib", "--",
        *verus_args,
    ]

    metadata = {
        "label": args.label,
        "crate": str(crate),
        "module": args.module,
        "threads": args.threads,
        "command": command,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "host": platform.node(),
        "revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root.parent, text=True
        ).strip(),
    }
    start = time.monotonic()
    process = subprocess.run(command, cwd=crate, text=True, capture_output=True)
    metadata["wall_seconds"] = time.monotonic() - start
    metadata["exit_code"] = process.returncode
    metadata["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out / "stdout.log").write_text(process.stdout)
    (out / "stderr.log").write_text(process.stderr)
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, indent=2))
    if process.returncode:
        print(process.stdout)
        print(process.stderr, file=os.sys.stderr)
        raise SystemExit(process.returncode)


if __name__ == "__main__":
    main()
