#!/usr/bin/env python3
"""Measure CMS encoder phases and optionally collect macOS sampling profiles."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import platform
import random
import subprocess
import time
import uuid

from common import RESULTS, ROOT, environment_info, fingerprint, machine_info, save


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=float, default=5.0)
    parser.add_argument("--seed", type=int, default=1234)
    parser.add_argument("--sample", action="store_true", help="also run macOS sample (requires permission to inspect child processes)")
    args = parser.parse_args()
    if args.seconds < 2 or not args.seconds < 3600:
        parser.error("--seconds must be in [2, 3600)")
    if args.sample and platform.system() != "Darwin":
        parser.error("--sample is macOS-only; use perf or another profiler with the example on Linux")
    command = ["cargo", "build", "--locked", "-p", "vest_bench", "--profile", "profiling",
               "--example", "cms_profile", "--message-format=json"]
    build = subprocess.run(command, cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE)
    binary = next(json.loads(line)["executable"] for line in build.stdout.splitlines()
                  if json.loads(line).get("executable") and json.loads(line).get("target", {}).get("name") == "cms_profile")
    directory = RESULTS / "profiles" / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8])
    directory.mkdir(parents=True)
    jobs = [(workload, implementation, phase)
            for workload in ("content_info", "real_signed_data")
            for implementation, phases in (("vest", ("prepare", "length", "write", "total")),
                                          ("rustcrypto", ("length", "write", "total")), ("rasn", ("total",)))
            for phase in phases]
    random.Random(args.seed).shuffle(jobs)
    manifest = {"status": "running", "fingerprint": fingerprint(), "machine": machine_info(),
                "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "environment": environment_info(),
                "rustc": subprocess.check_output(["rustc", "-Vv"], text=True).strip(),
                "build": command, "profile": "bench settings plus debug symbols", "seed": args.seed,
                "sampled": args.sample, "measurements": [], "order": jobs}
    save(directory / "profile.json", manifest)
    print(f"Profile directory: {directory}", flush=True)
    try:
        for workload, implementation, phase in jobs:
            name = f"{workload}-{implementation}-{phase}"
            ready = directory / f"{name}.ready"
            command = [binary, implementation, phase, "--workload", workload, "--seconds", str(args.seconds),
                       "--ready-file", str(ready)]
            print(name, flush=True)
            with (directory / f"{name}.log").open("w") as log:
                process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
                try:
                    deadline = time.monotonic() + 120
                    while not ready.is_file():
                        if process.poll() is not None or time.monotonic() > deadline:
                            raise RuntimeError(f"{name}: setup failed or timed out; see its log")
                        time.sleep(0.05)
                    if args.sample:
                        subprocess.run(["sample", str(process.pid), "1", "1", "-file", str(directory / f"{name}.sample.txt")],
                                       check=True, stdout=subprocess.DEVNULL, timeout=30)
                    if process.wait(timeout=args.seconds + 30) != 0:
                        raise RuntimeError(f"{name}: profiling failed; see its log")
                finally:
                    if process.poll() is None:
                        process.terminate()
                        process.wait(timeout=10)
                ready.unlink(missing_ok=True)
            result = json.loads((directory / f"{name}.log").read_text().splitlines()[-1])
            manifest["measurements"].append(result)
            save(directory / "profile.json", manifest)
            print(f"  {result['median_ns'] / 1e6:.3f} ms/pass", flush=True)
        if fingerprint() != manifest["fingerprint"]:
            raise RuntimeError("sources changed during profiling")
        manifest["status"] = "complete"
        save(directory / "profile.json", manifest)
    except BaseException as error:
        manifest.update(status="failed", error=str(error))
        save(directory / "profile.json", manifest)
        raise


if __name__ == "__main__":
    main()
