#!/usr/bin/env python3
"""Generate and verify matched Vest/VPS depth and width stress formats."""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


def depth_schema(n: int) -> str:
    definitions = ["depth0 = {\n    value: u8,\n}\n"]
    for i in range(1, n + 1):
        definitions.append(f"depth{i} = {{\n    value: depth{i - 1},\n}}\n")
    return "\n".join(definitions)


def struct_schema(n: int) -> str:
    fields = "\n".join(f"    field{i}: u8," for i in range(n))
    return f"struct_width{n} = {{\n{fields}\n}}\n"


def choice_schema(n: int) -> str:
    if n < 2 or n > 256:
        raise ValueError("choice width must be in 2..=256 for distinct u8 tags")
    variants = [f"    Variant{i}(u8 | {i})," for i in range(n - 1)]
    variants.append(f"    Variant{n - 1}(u8 | {n - 1}..),")
    return f"choice_width{n} = choose {{\n" + "\n".join(variants) + "\n}\n"


def run_case(repo: Path, out_root: Path, system: str, kind: str, size: int,
             threads: int, timeout: int) -> dict[str, object]:
    case = out_root / system / f"{kind}-{size}"
    crate = case / "crate"
    src = crate / "src"
    src.mkdir(parents=True, exist_ok=True)
    schema = {
        "depth": depth_schema,
        "struct": struct_schema,
        "choice": choice_schema,
    }[kind](size)
    schema_path = case / "schema.vest"
    schema_path.write_text(schema)

    if system == "vest":
        compiler = repo / "baselines" / "vest-dsl" / "Cargo.toml"
        library = repo / "baselines" / "vest-lib"
        dependency = "vest_lib"
    else:
        compiler = repo / "vest-dsl-vps" / "Cargo.toml"
        library = repo / "vps-lib"
        dependency = "vps_lib"

    generated = src / "generated.rs"
    compile_cmd = [
        "cargo", "run", "--quiet", "--manifest-path", str(compiler), "--",
        str(schema_path), "--output", str(generated),
    ]
    compile_start = time.monotonic()
    compile_result = subprocess.run(compile_cmd, cwd=repo, text=True, capture_output=True)
    compile_wall = time.monotonic() - compile_start
    (case / "codegen.stdout.log").write_text(compile_result.stdout)
    (case / "codegen.stderr.log").write_text(compile_result.stderr)
    if compile_result.returncode:
        return {
            "system": system, "kind": kind, "size": size,
            "codegen_wall_seconds": compile_wall, "codegen_exit_code": compile_result.returncode,
            "verify_exit_code": None,
        }

    relative_library = os.path.relpath(library, crate)
    dependency_line = (
        f'{dependency} = {{ package = "vps-lib", path = "{relative_library}" }}\n'
        if system == "vps"
        else f'{dependency} = {{ path = "{relative_library}" }}\n'
    )
    (crate / "Cargo.toml").write_text(
        "[package]\nname = \"vps-scalability-case\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n"
        "[dependencies]\n"
        f"vstd = \"=0.0.0-2026-07-27-0206\"\n"
        f"{dependency_line}\n"
        "[package.metadata.verus]\nverify = true\n"
    )
    # Use the same explicit ceiling for both systems so a deeply nested Rust
    # type is measured rather than rejected by rustc's conservative default.
    (src / "lib.rs").write_text("#![recursion_limit = \"512\"]\npub mod generated;\n")
    verify_cmd = [
        "cargo", "verus", "verify", "--fwd-verus-args-to", "roots", "--lib", "--",
        "--verify-module", "generated", "--time-expanded", "--output-json",
        "--num-threads", str(threads),
    ]
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(out_root / "target" / system)
    verify_start = time.monotonic()
    process = subprocess.Popen(
        verify_cmd, cwd=crate, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        verify_exit: int | str = process.returncode
    except subprocess.TimeoutExpired:
        verify_exit = "timeout"
        # Cargo spawns rustc, Verus, and the SMT solver. Killing only Cargo can
        # leave descendants holding the capture pipes open indefinitely.
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
    verify_wall = time.monotonic() - verify_start
    if isinstance(stdout, bytes):
        stdout = stdout.decode(errors="replace")
    if isinstance(stderr, bytes):
        stderr = stderr.decode(errors="replace")
    (case / "verify.stdout.log").write_text(stdout)
    (case / "verify.stderr.log").write_text(stderr)
    result = {
        "system": system,
        "kind": kind,
        "size": size,
        "generated_sloc": sum(bool(x.strip()) for x in generated.read_text().splitlines()),
        "codegen_wall_seconds": compile_wall,
        "codegen_exit_code": compile_result.returncode,
        "verify_wall_seconds": verify_wall,
        "verify_exit_code": verify_exit,
        "threads": threads,
        "timeout_seconds": timeout,
        "rust_recursion_limit": 512,
    }
    if verify_exit == 0:
        json_start = stdout.find("{")
        if json_start < 0:
            raise ValueError(f"successful Verus run emitted no JSON report for {system}/{kind}-{size}")
        report, _ = json.JSONDecoder().raw_decode(stdout, json_start)
        times = report["times-ms"]
        result.update({
            "verified_vcs": report["verification-results"]["verified"],
            "verus_total_seconds": times["total"] / 1000,
            "rust_seconds": times["rust"]["total"] / 1000,
            "verification_wall_seconds": times["verification"]["total"] / 1000,
            "verification_cpu_seconds": times["total-verify"] / 1000,
            "smt_cpu_seconds": times["smt"]["total"] / 1000,
        })
    (case / "metadata.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main() -> None:
    eval_root = Path(__file__).resolve().parents[1]
    repo = eval_root.parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--systems", nargs="+", choices=["vest", "vps"], default=["vest", "vps"])
    parser.add_argument("--kind", choices=["depth", "struct", "choice"], required=True)
    parser.add_argument("--sizes", nargs="+", type=int, required=True)
    parser.add_argument("--threads", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = eval_root / "results" / "raw" / "scalability" / stamp
    results = []
    # Populate the compiler, dependency, and shared Cargo target caches before
    # recording any case. The warm-up is retained on disk but excluded from the
    # summary.
    for system in args.systems:
        warm = run_case(repo, out, system, "depth", 0, args.threads, args.timeout)
        if warm.get("verify_exit_code") != 0:
            raise RuntimeError(f"{system} warm-up failed: {warm}")
    for size in args.sizes:
        for system in args.systems:
            result = run_case(repo, out, system, args.kind, size, args.threads, args.timeout)
            results.append(result)
            print(json.dumps(result))
    (out / "summary.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Raw scalability artifacts: {out}")


if __name__ == "__main__":
    main()
