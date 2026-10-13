#!/usr/bin/env python3
"""List, measure, and report isolated Criterion comparisons."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import re
import statistics
import subprocess
import sys
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "target/vest-bench"
VERSION = 3
BEGIN, END = "<!-- benchmark-results:start -->", "<!-- benchmark-results:end -->"
SOURCE_ROOTS = {"vest_bench", "vest_lib", "vest_tests", "vest_asn1_tests", "Cargo.toml", "Cargo.lock", ".cargo"}


def save(path, value):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def fingerprint():
    names = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT
    ).decode().split("\0")
    digest = hashlib.sha256()
    for name in sorted(set(names) - {""}):
        path = ROOT / name
        if (Path(name).parts[0] in SOURCE_ROOTS and path.is_file()
                and path.suffix.lower() not in {".md", ".xz", ".png", ".svg"}):
            digest.update(name.encode() + b"\0" + path.read_bytes())
    return digest.hexdigest()


def machine_info():
    info = {"platform": platform.platform(), "logical_cpus": os.cpu_count()}
    if platform.system() == "Darwin":
        info["cpu"] = subprocess.check_output(["sysctl", "-n", "machdep.cpu.brand_string"], text=True).strip()
        info["ram_bytes"] = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True))
    else:
        models = [line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                  if line.startswith(("model name", "Hardware", "Processor"))]
        info["cpu"] = models[0] if models else platform.machine()
        info["ram_bytes"] = int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) * 1024
    return info


def build(targets, allocations=False):
    metadata = json.loads(subprocess.check_output(
        ["cargo", "metadata", "--locked", "--no-deps", "--format-version=1"], cwd=ROOT, text=True))
    package = next(p for p in metadata["packages"] if p["name"] == "vest_bench")
    available = {t["name"] for t in package["targets"] if "bench" in t["kind"]}
    names = {t.split("/")[0] for t in targets} if targets else available
    if not names <= available:
        raise ValueError(f"unknown benchmark families: {names - available}")
    command = ["cargo", "bench", "--locked", "-p", "vest_bench", "--no-run", "--message-format=json"]
    if allocations:
        command += ["--features", "vest_bench/allocation-counting"]
    for name in sorted(names):
        command += ["--bench", name]
    output = subprocess.check_output(command, cwd=ROOT, text=True)
    artifacts = [json.loads(line) for line in output.splitlines() if line.startswith("{")]
    binaries = {a["target"]["name"]: a["executable"] for a in artifacts
                if a.get("executable") and a["target"]["name"] in names}
    if binaries.keys() != names:
        raise ValueError("missing benchmark binaries")
    return binaries


def select(entries, targets):
    def matches(identity, prefix):
        return identity == prefix or identity.startswith(prefix.rstrip("/") + "/")
    for target in targets:
        if not any(matches(e["id"], target) for e in entries):
            raise ValueError(f"unknown target prefix: {target}")
    return [e for e in entries if not targets or any(matches(e["id"], t) for t in targets)]


def workload_list(entries, targets):
    selected = {e["id"].rsplit("/", 2)[0] for e in select(entries, targets)}
    workloads = {}
    for entry in entries:
        name, operation, _ = entry["id"].rsplit("/", 2)
        if name in selected and (name not in workloads or operation == "parse"):
            workloads[name] = (entry["items"], entry["bytes"])
    rows = [(name, f"{items} items", f"{size} bytes") for name, (items, size) in sorted(workloads.items())]
    widths = [max(len(row[i]) for row in rows) for i in range(3)]
    return "\n".join(f"{name:<{widths[0]}}  {items:>{widths[1]}}  {size:>{widths[2]}}" for name, items, size in rows)


def inventory(binaries, directory, timeout):
    entries = []
    for family, binary in sorted(binaries.items()):
        path = directory / f"inventory-{family}.jsonl"
        env = dict(os.environ, VEST_BENCH_INVENTORY=str(path))
        output = subprocess.check_output([binary, "--list"], cwd=ROOT, env=env, text=True, timeout=timeout)
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        ids = {row["id"] for row in rows}
        listed = {line.removesuffix(": benchmark") for line in output.splitlines() if line.endswith(": benchmark")}
        if len(ids) != len(rows) or ids != listed:
            raise ValueError(f"{family}: duplicate or missing inventory registrations")
        entries += rows
    return entries


def capture(directory, identity):
    matches = []
    for path in directory.glob("**/new/benchmark.json"):
        data = json.loads(path.read_text())
        if f"{data['group_id']}/{data['function_id']}" == identity:
            matches.append(path.parent)
    if len(matches) != 1:
        raise ValueError(f"expected one measurement for {identity}, found {len(matches)}")
    return {"id": identity, "directory": str(matches[0].relative_to(directory))}


def publish(directory, manifest):
    if manifest["status"] != "complete":
        raise ValueError("cannot publish an incomplete run")
    save(directory / "run.json", manifest)
    if not manifest["targets"] and not manifest["quick"]:
        save(RESULTS / "latest.json", {"run": str(directory.relative_to(RESULTS))})


def execute(args):
    directory = RESULTS / "runs" / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8])
    directory.mkdir(parents=True)
    (directory / "logs").mkdir()
    env_keys = {"RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTUP_TOOLCHAIN", "RUSTC",
                "RUSTC_WRAPPER", "MACOSX_DEPLOYMENT_TARGET", "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET"}
    manifest = {
        "version": VERSION, "status": "running", "fingerprint": fingerprint(),
        "started": datetime.now(timezone.utc).isoformat(), "quick": args.quick, "targets": args.targets,
        "seed": args.seed if args.seed is not None else random.SystemRandom().randrange(2**32),
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
        "rustc": subprocess.check_output(["rustc", "-Vv"], text=True).strip(), "machine": machine_info(),
        "environment": {k: v for k, v in os.environ.items() if k in env_keys or k.startswith("CARGO_PROFILE_")},
        "settings": {"samples": 10 if args.quick else 100, "warmup_seconds": .1 if args.quick else 3,
                     "measurement_seconds": .2 if args.quick else 5},
        "jobs": [], "measurements": [], "allocations": {} if args.allocations else None,
    }
    save(directory / "run.json", manifest)
    print(f"Run directory: {directory}", flush=True)
    try:
        binaries = build(args.targets)
        jobs = select(inventory(binaries, directory, args.timeout), args.targets)
        random.Random(manifest["seed"]).shuffle(jobs)
        manifest["jobs"] = jobs
        env = dict(os.environ, CRITERION_HOME=str(directory / "criterion"))
        for index, job in enumerate(jobs, 1):
            identity = job["id"]
            print(f"[{index}/{len(jobs)}] {identity}", flush=True)
            command = [binaries[identity.split("/")[0]], "^" + re.escape(identity) + "$", "--bench", "--noplot"]
            if args.quick:
                command += ["--sample-size", "10", "--warm-up-time", ".1", "--measurement-time", ".2"]
            with (directory / "logs" / f"{index:03d}.log").open("w") as log:
                subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                               timeout=args.timeout, check=True)
            manifest["measurements"].append(capture(directory / "criterion", identity))
            save(directory / "run.json", manifest)
        if args.allocations:
            for family, binary in build(args.targets, allocations=True).items():
                selected = {job["id"] for job in jobs if job["id"].startswith(family + "/")}
                path = directory / f"allocations-{family}.jsonl"
                expression = "^(?:" + "|".join(re.escape(i) for i in sorted(selected)) + ")$"
                with (directory / "logs" / f"alloc-{family}.log").open("w") as log:
                    subprocess.run([binary, expression, "--test"], cwd=ROOT,
                                   env=dict(env, VEST_BENCH_ALLOCATIONS=str(path)), stdout=log,
                                   stderr=subprocess.STDOUT, timeout=args.timeout, check=True)
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                if len(rows) != len(selected) or {row["id"] for row in rows} != selected:
                    raise ValueError(f"{family}: incomplete allocation audit")
                manifest["allocations"].update({row.pop("id"): row for row in rows})
        if fingerprint() != manifest["fingerprint"]:
            raise ValueError("sources or corpus changed during measurement")
        manifest.update(status="complete", finished=datetime.now(timezone.utc).isoformat())
        publish(directory, manifest)
        print(f"Report with: python3 scripts/bench.py report --run {directory}")
    except BaseException as error:
        manifest.update(status="failed", error=str(error))
        save(directory / "run.json", manifest)
        raise


@dataclass(frozen=True)
class Measurement:
    id: str
    median: float
    lower: float
    upper: float
    bytes: int
    items: int
    samples: tuple[float, ...]

    def rate(self, ns):
        return self.bytes * 1e9 / ns / 2**20


def load_run(directory):
    manifest = json.loads((directory / "run.json").read_text())
    if manifest["version"] != VERSION or manifest["status"] != "complete":
        raise ValueError("unsupported or incomplete run; use a new run")
    if manifest["fingerprint"] != fingerprint():
        raise ValueError("sources/corpora differ; rerun benchmarks")
    jobs = {j["id"]: j for j in manifest["jobs"]}
    records = {r["id"]: r for r in manifest["measurements"]}
    if (len(jobs) != len(manifest["jobs"]) or len(records) != len(manifest["measurements"])
            or jobs.keys() != records.keys()
            or manifest["allocations"] is not None and manifest["allocations"].keys() != jobs.keys()):
        raise ValueError("duplicate or missing measurements/audits")
    rows = []
    criterion = (directory / "criterion").resolve()
    for identity, job in jobs.items():
        raw = (criterion / records[identity]["directory"]).resolve()
        if not raw.is_relative_to(criterion):
            raise ValueError("measurement path escapes run")
        data = json.loads((raw / "benchmark.json").read_text())
        if f"{data['group_id']}/{data['function_id']}" != identity or data["throughput"]["Bytes"] != job["bytes"]:
            raise ValueError(f"workload mismatch: {identity}")
        median = json.loads((raw / "estimates.json").read_text())["median"]
        ci = median["confidence_interval"]
        sample = json.loads((raw / "sample.json").read_text())
        samples = tuple(t / n for t, n in zip(sample["times"], sample["iters"], strict=True))
        rows.append(Measurement(identity, median["point_estimate"], ci["lower_bound"],
                                ci["upper_bound"], job["bytes"], job["items"], samples))
    return manifest, rows


def ratio(vest, baseline):
    if (vest.bytes, vest.items) != (baseline.bytes, baseline.items):
        raise ValueError("unequal comparison workloads")
    rng = random.Random(vest.id + baseline.id)
    samples = sorted(statistics.median(rng.choices(baseline.samples, k=len(baseline.samples))) /
                     statistics.median(rng.choices(vest.samples, k=len(vest.samples))) for _ in range(2000))
    bounds = statistics.quantiles(samples, n=40, method="inclusive")
    return f"{baseline.median / vest.median:.2f}× [{bounds[0]:.2f}–{bounds[-1]:.2f}]"


def rate(m):
    return f"{m.rate(m.median):,.1f} [{m.rate(m.upper):,.1f}–{m.rate(m.lower):,.1f}]"


def tables(rows, compact=False):
    lines = []
    groups = sorted({r.id.rsplit("/", 1)[0] for r in rows}, key=lambda g: (not g.startswith("micro/"), g))
    if any(g.startswith("micro/") for g in groups):
        lines += ["### Microformats", ""]
    keys = [("micro/" + op, [g for g in groups if g.startswith("micro/") and g.endswith("/" + op)])
            for op in ("parse", "serialize") if any(g.startswith("micro/") and g.endswith("/" + op) for g in groups)]
    keys += [(g, [g]) for g in groups if not g.startswith("micro/")]
    for title, members in keys:
        micro = title.startswith("micro/")
        header = (["Format"] if micro else []) + ["Implementation"]
        header += ([] if compact else ["Median per pass (µs) [95% CI]"]) + ["MiB/s [95% CI]", "Vest/baseline [95% CI]"]
        if not compact:
            header += ["ns/item"]
        lines += [("#### " + title.split("/")[1].capitalize()) if micro else "### " + title, "",
                  "| " + " | ".join(header) + " |", "| " + " | ".join(["---"] * len(header)) + " |"]
        for group in members:
            entries = sorted((r for r in rows if r.id.rsplit("/", 1)[0] == group), key=lambda r: (not r.id.endswith("/Vest"), r.id))
            vest = next((r for r in entries if r.id.endswith("/Vest")), None)
            for m in entries:
                cells = ([f"`{m.id.split('/')[1]}`"] if micro else []) + [m.id.split("/")[-1]]
                if not compact:
                    cells += [f"{m.median / 1000:.2f} [{m.lower / 1000:.2f}–{m.upper / 1000:.2f}]"]
                cells += [rate(m), ratio(vest, m) if vest and m is not vest else "—"]
                if not compact:
                    cells += [f"{m.median / m.items:,.1f}"]
                lines.append("| " + " | ".join(cells) + " |")
        lines.append("")
    return "\n".join(lines)


def render(manifest, rows, directory, compact=False):
    machine, settings = manifest["machine"], manifest["settings"]
    ram = f"{machine['ram_bytes'] / 2**30:g} GiB" if machine["ram_bytes"] else "Not recorded"
    meta = [("Run", directory.name), ("CPU", machine["cpu"]), ("RAM", ram),
            ("Platform", machine["platform"]), ("Logical CPUs", machine["logical_cpus"]),
            ("Compiler", manifest["rustc"].splitlines()[0]), ("Commit", manifest["commit"]),
            ("Uncommitted files", "Yes" if manifest["dirty"] else "No"), ("Source/corpus SHA256", manifest["fingerprint"]),
            ("Sampling", f"{settings['samples']} samples; {settings['warmup_seconds']:g} s warmup; {settings['measurement_seconds']:g} s target"),
            ("Process-order seed", manifest["seed"]), ("Coverage", f"{len(rows)} of {len(manifest['jobs'])} entries"),
            ("Allocator", "std::alloc::System; counted separately, without timing")]
    lines = ["| Setting | Value |", "| --- | --- |"] + [f"| {k} | {v} |" for k, v in meta]
    if manifest["quick"]:
        lines += ["", "**Quick validation run—not final performance measurements.**"]
    lines += ["", "Ratios are Vest/baseline throughput. 95% intervals describe within-run sampling noise, not between-run variability.",
              "", tables(rows, compact)]
    warnings = sorted({line.strip() for log in (directory / "logs").glob("*.log")
                       for line in log.read_text().splitlines() if line.startswith("Warning:")})
    if not compact and warnings:
        lines += ["### Criterion warnings", ""] + [f"- {warning}" for warning in warnings] + [""]
    if not compact and manifest["allocations"] is not None:
        lines += ["### Untimed allocation audit", "", "Requests are cumulative, not peak memory; result storage and final destruction are excluded.", "",
                  "| Benchmark | Allocations | Reallocations | Requested bytes | Deallocations |", "| --- | --- | --- | --- | --- |"]
        selected = {row.id for row in rows}
        for identity, c in sorted(manifest["allocations"].items()):
            if identity in selected:
                lines.append(f"| {identity} | {c['allocations']} | {c['reallocations']} | {c['requested_bytes']} | {c['deallocations']} |")
    return "\n".join(lines) + "\n"


def write_reports(directory, manifest, rows):
    if (manifest["quick"] or manifest["targets"]
            or manifest["fingerprint"] != fingerprint() or not manifest["machine"]["ram_bytes"]
            or not manifest["machine"]["cpu"]):
        raise ValueError("publishing requires a current-source, whole-suite, non-quick run with hardware metadata")
    path = ROOT / "vest_bench/results" / (manifest["started"][:10] + ".md")
    readme = ROOT / "vest_bench/README.md"
    text = readme.read_text()
    before, rest = text.split(BEGIN)
    _, after = rest.split(END)
    path.write_text("# Benchmark results\n\nAuto-generated by `python3 -B scripts/bench.py report --write`; do not edit by hand.\n\n"
                    + render(manifest, rows, directory))
    summary = f"Full results: [`{path.name}`](results/{path.name}).\n\n"
    readme.write_text(before + BEGIN + "\n\n" + summary + render(manifest, rows, directory, True) + "\n" + END + after)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("list", "run", "report"):
        command = commands.add_parser(name)
        command.add_argument("targets", nargs="*", help="ID prefixes, e.g. micro/bits or tls")
        if name != "report":
            command.add_argument("--timeout", type=int, default=300)
        if name == "run":
            command.add_argument("--seed", type=int)
            command.add_argument("--quick", action="store_true")
            command.add_argument("--allocations", action="store_true")
        if name == "report":
            command.add_argument("--run", type=Path)
            command.add_argument("--write", action="store_true", help="refresh result snapshot and README together")
    args = parser.parse_args()
    try:
        if args.command != "report" and args.timeout <= 0:
            raise ValueError("--timeout must be positive")
        if args.command == "run":
            execute(args)
        elif args.command == "list":
            with tempfile.TemporaryDirectory() as temporary:
                entries = inventory(build(args.targets), Path(temporary), args.timeout)
            print(workload_list(entries, args.targets))
        else:
            directory = args.run or RESULTS / json.loads((RESULTS / "latest.json").read_text())["run"]
            manifest, rows = load_run(directory)
            selected = {e["id"] for e in select(manifest["jobs"], args.targets)}
            if args.write:
                if args.targets:
                    raise ValueError("--write cannot publish a filtered report")
                write_reports(directory, manifest, rows)
            print(render(manifest, [r for r in rows if r.id in selected], directory))
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
