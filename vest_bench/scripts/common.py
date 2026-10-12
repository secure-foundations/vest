"""Benchmark inventory, build configuration, and run provenance."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "target" / "vest-bench"
POLICY = "prepare-retained-drop-natural-output-v1"
MICROFORMATS = ("flat", "table", "nest", "tlv", "varint", "bits", "bounded_list", "tail_list")
SUITES = ("formats", "tls", "bitcoin", "cms", "cbor")


def fingerprint() -> str:
    """Hash working-tree sources, dependencies, and corpora, including dirty files."""
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT
    ).decode().split("\0")
    digest = hashlib.sha256()
    for name in sorted(set(paths)):
        if not name:
            continue
        path = Path(name)
        if path.parts[0] not in {
            "vest_bench", "vest_lib", "vest_tests", "vest_asn1_tests", "Cargo.toml", "Cargo.lock", ".cargo"
        }:
            continue
        if path.suffix.lower() in {".md", ".xz", ".png", ".svg"}:
            continue
        full = ROOT / path
        if not full.is_file():
            # Deleted index entries disappear on commit. Hash the actual
            # working tree so committing unchanged sources preserves the hash.
            continue
        digest.update(name.encode() + b"\0")
        digest.update(full.read_bytes())
    return digest.hexdigest()


def jobs(targets: list[str]) -> list[tuple[str, str]]:
    selected = set(targets or SUITES)
    result = []
    for name in MICROFORMATS:
        if "formats" in selected or name in selected:
            result.extend(("formats", f"{name}/{op}/{impl}") for op in ("parse", "serialize") for impl in ("vest", "hand"))
    if "tls" in selected:
        result.extend(("tls", f"tls/{name}/{op}/{impl}") for name in (
            "client_hello", "server_hello", "encrypted_extensions", "certificate", "certificate_verify", "finished", "new_session_ticket"
        ) for op in ("parse", "serialize") for impl in ("Vest", "Rustls"))
    if "bitcoin" in selected:
        result.extend(("bitcoin", f"bitcoin/{op}/{impl}") for op in ("parse", "serialize") for impl in ("Vest", "rust-bitcoin"))
    if "cms" in selected:
        for name in ("content_info", "real_signed_data"):
            implementations = ["Vest", "rasn-cms", "RustCrypto-cms"]
            if name == "content_info": implementations.append("cryptographic-message-syntax")
            result.extend(("cms", f"cms/{name}/{op}/{impl}") for op in ("parse", "serialize") for impl in implementations)
    if "cbor" in selected:
        for name in ("synthetic", "synthetic_definite", "cose"):
            for op in ("parse", "serialize"):
                implementations = ["Vest", "ciborium", "cbor4ii"]
                if name != "cose": implementations.append("minicbor-serde")
                if name == "synthetic" and op == "parse": implementations.remove("cbor4ii")
                result.extend(("cbor", f"cbor/{name}/{op}/{impl}") for impl in implementations)
    return result


def build(suites: set[str], *, allocations: bool, offline: bool = False) -> dict[str, str]:
    command = ["cargo", "bench", "--locked", "-p", "vest_bench", "--no-run", "--message-format=json"]
    if offline:
        command.append("--offline")
    if allocations: command += ["--features", "vest_bench/allocation-counting"]
    for suite in sorted(suites): command += ["--bench", suite]
    # stderr remains visible: do not bury a compiler error in a benchmark log.
    process = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    binaries = {}
    for line in process.stdout.splitlines():
        try: artifact = json.loads(line)
        except json.JSONDecodeError: continue
        if artifact.get("reason") == "compiler-artifact" and artifact.get("executable"):
            name = artifact["target"]["name"]
            if name in suites: binaries[name] = artifact["executable"]
    if binaries.keys() != suites:
        raise RuntimeError(f"missing benchmark executables: {suites - binaries.keys()}")
    return binaries


def external_corpus() -> dict | None:
    """Record the actual external input, not just its environment-variable name."""
    value = os.environ.get("VEST_BENCH_BITCOIN_CORPUS")
    if not value:
        return None
    path = Path(value).resolve()
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def environment_info() -> dict[str, str]:
    keys = {"RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTUP_TOOLCHAIN", "RUSTC", "RUSTC_WRAPPER",
            "MACOSX_DEPLOYMENT_TARGET", "VEST_BENCH_BITCOIN_CORPUS", "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET"}
    return {k: v for k, v in os.environ.items() if k in keys or k.startswith("CARGO_PROFILE_")}


def external_corpus_matches(recorded: dict | None) -> bool:
    if not recorded:
        return True
    try:
        return hashlib.sha256(Path(recorded["path"]).read_bytes()).hexdigest() == recorded["sha256"]
    except OSError:
        return False


def validate_inventory(binaries: dict[str, str], env: dict[str, str]) -> None:
    """Fail when the driver's job matrix drifts from the registered benchmarks."""
    for suite, binary in binaries.items():
        output = subprocess.check_output([binary, "--list"], cwd=ROOT, env=env, text=True)
        actual = {line.removesuffix(": benchmark") for line in output.splitlines() if line.endswith(": benchmark")}
        expected = {identity for _, identity in jobs([suite])}
        if actual != expected:
            raise RuntimeError(f"{suite} inventory changed: missing={expected - actual}, unregistered={actual - expected}")


def save(path: Path, data: dict) -> None:
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def machine_info() -> dict:
    machine = {"platform": platform.platform(), "logical_cpus": os.cpu_count(), "cpu": platform.processor()}
    if platform.system() == "Darwin":
        for key, command in (("cpu", "machdep.cpu.brand_string"), ("ram_bytes", "hw.memsize")):
            value = subprocess.run(["sysctl", "-n", command], capture_output=True, text=True)
            machine[key] = value.stdout.strip() if value.returncode == 0 else "unavailable (restricted environment)"
        machine["macos"] = platform.mac_ver()[0]
    elif Path("/proc/cpuinfo").is_file():
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                machine["cpu"] = line.split(":", 1)[1].strip()
                break
        machine["memory"] = Path("/proc/meminfo").read_text().splitlines()[0]
    return machine
