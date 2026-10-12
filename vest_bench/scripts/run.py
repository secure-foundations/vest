#!/usr/bin/env python3
"""Run isolated Criterion comparisons and save their provenance together."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import random
import re
import subprocess
import time
import uuid

from common import (MICROFORMATS, POLICY, RESULTS, ROOT, SUITES, build, environment_info, external_corpus,
                    external_corpus_matches, fingerprint, jobs, machine_info, save, validate_inventory)


def capture_estimate(directory: Path, job: str, started_ns: int) -> dict:
    for path in directory.glob("**/new/benchmark.json"):
        benchmark = json.loads(path.read_text())
        if benchmark["group_id"] + "/" + benchmark["function_id"] != job: continue
        files = [path, path.with_name("estimates.json"), path.with_name("sample.json")]
        if any(not p.is_file() or p.stat().st_mtime_ns < started_ns for p in files):
            raise RuntimeError(f"no fresh measurements for {job}")
        return {"id": job, "files": {
            str(p.relative_to(directory)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files
        }}
    raise RuntimeError(f"benchmark filter did not produce {job}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", choices=[*SUITES, *MICROFORMATS])
    parser.add_argument("--seed", type=int, default=None, help="reproduce the randomized process order")
    parser.add_argument("--allocations", action="store_true", help="also run a separate untimed allocator audit")
    parser.add_argument("--quick", action="store_true", help="short validation measurements, not publication results")
    parser.add_argument("--list", action="store_true", help="list the selected measurements without running them")
    parser.add_argument("--offline", action="store_true", help="use cached Cargo dependencies only")
    parser.add_argument("--timeout", type=float, default=300, help="maximum seconds for each benchmark process")
    args = parser.parse_args()
    selected_jobs = jobs(args.targets)
    if args.list:
        print("\n".join(identity for _, identity in selected_jobs))
        return
    if not 0 < args.timeout < float("inf"):
        parser.error("--timeout must be positive and finite")
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(2**32)
    random.Random(seed).shuffle(selected_jobs)
    directory = RESULTS / "runs" / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8])
    directory.mkdir(parents=True)
    criterion_dir = directory / "criterion"
    manifest = {
        "policy": POLICY, "fingerprint": fingerprint(), "status": "running", "quick": args.quick,
        "started": datetime.now(timezone.utc).isoformat(), "seed": seed, "targets": args.targets or list(SUITES),
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "dirty": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True),
        "rustc": subprocess.check_output(["rustc", "-Vv"], cwd=ROOT, text=True).strip(),
        "machine": machine_info(),
        "allocator": "std::alloc::System; counting wrapper enabled only in separate untimed audit binaries",
        "environment": environment_info(),
        "external_corpus": external_corpus(),
        "settings": {"samples": 10 if args.quick else 100, "warmup_seconds": 0.1 if args.quick else 3,
                     "measurement_seconds": 0.2 if args.quick else 5},
        "jobs": [job for _, job in selected_jobs], "measurements": [], "allocations": {},
    }
    save(directory / "run.json", manifest)
    print(f"Run directory: {directory}", flush=True)
    try:
        subprocess.run(["cargo", "test", "--locked", "-p", "vest_bench", *(["--offline"] if args.offline else [])], cwd=ROOT, check=True)
        binaries = build({suite for suite, _ in selected_jobs}, allocations=False, offline=args.offline)
        manifest["binaries"] = {suite: {"path": path, "sha256": hashlib.sha256(Path(path).read_bytes()).hexdigest()}
                                for suite, path in binaries.items()}
        env = dict(os.environ, VEST_BENCH_CRITERION_DIR=str(criterion_dir))
        validate_inventory(binaries, env)
        for index, (suite, job) in enumerate(selected_jobs, 1):
            print(f"[{index}/{len(selected_jobs)}] {job}", flush=True)
            started_ns = time.time_ns()
            metadata = directory / "corpus-pass.json"
            metadata.unlink(missing_ok=True)
            job_env = dict(env, VEST_BENCH_JOB=job, VEST_BENCH_METADATA_FILE=str(metadata))
            command = [binaries[suite], "^" + re.escape(job) + "$", "--bench", "--noplot"]
            if args.quick: command += ["--sample-size", "10", "--warm-up-time", "0.1", "--measurement-time", "0.2"]
            with (directory / f"{index:03d}.log").open("w") as log:
                subprocess.run(command, cwd=ROOT, env=job_env, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
            measurement = capture_estimate(criterion_dir, job, started_ns)
            if metadata.is_file(): measurement["corpus"] = json.loads(metadata.read_text())
            manifest["measurements"].append(measurement)
            save(directory / "run.json", manifest)
        metadata.unlink(missing_ok=True)
        if args.allocations:
            audit_binaries = build({suite for suite, _ in selected_jobs}, allocations=True, offline=args.offline)
            for index, (suite, job) in enumerate(selected_jobs, 1):
                path = directory / "allocation-pass.json"
                path.unlink(missing_ok=True)
                audit_env = dict(env, VEST_BENCH_ALLOCATION_FILE=str(path))
                print(f"[allocations {index}/{len(selected_jobs)}] {job}", flush=True)
                with (directory / f"alloc-{index:03d}.log").open("w") as log:
                    subprocess.run([audit_binaries[suite], "^" + re.escape(job) + "$", "--test"],
                                   cwd=ROOT, env=audit_env, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
                manifest["allocations"][job] = json.loads(path.read_text())
            path.unlink(missing_ok=True)
        if fingerprint() != manifest["fingerprint"]:
            raise RuntimeError("sources or corpus changed during measurement; refusing to combine versions")
        if not external_corpus_matches(manifest["external_corpus"]):
            raise RuntimeError("external Bitcoin corpus changed during measurement")
        manifest["status"] = "complete"
        manifest["finished"] = datetime.now(timezone.utc).isoformat()
        save(directory / "run.json", manifest)
        pointer = "latest-quick.json" if args.quick else "latest.json"
        save(RESULTS / pointer, {"run": str(directory.relative_to(RESULTS))})
        print(f"Complete. Report with: python3 vest_bench/scripts/report.py --run {directory}")
    except BaseException as error:
        manifest["status"] = "failed"
        manifest["error"] = str(error)
        save(directory / "run.json", manifest)
        raise


if __name__ == "__main__":
    main()
