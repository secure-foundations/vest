#!/usr/bin/env python3
"""Produce reproducible source/proof-burden statistics for vest_lib2."""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path


PROOF_FN = re.compile(r"\b(?:broadcast\s+)?proof\s+fn\b")
SPEC_FN = re.compile(r"\b(?:(?:open|closed)\s+)?spec\s+fn\b")
EXEC_FN = re.compile(r"\bfn\s+[A-Za-z_][A-Za-z0-9_]*")
PROOF_BLOCK = re.compile(r"\bproof\s*\{")
CONTRACT = re.compile(
    r"^\s*(?:requires|ensures|recommends|decreases|invariant(?:_except_break)?)\b"
)


@dataclass
class Stats:
    category: str
    modules: int = 0
    total_sloc: int = 0
    spec_sloc: int = 0
    proof_sloc: int = 0
    exec_sloc: int = 0
    shared_sloc: int = 0
    spec_fns: int = 0
    proof_fns: int = 0
    exec_fns: int = 0
    format_types: int = 0
    spec_parser_impls: int = 0
    parser_impls: int = 0
    serializer_impls: int = 0

    def add(self, other: "Stats") -> None:
        for field in self.__dataclass_fields__:
            if field != "category":
                setattr(self, field, getattr(self, field) + getattr(other, field))

    def row(self) -> dict[str, object]:
        result = asdict(self)
        result["proof_to_code"] = (
            (self.spec_sloc + self.proof_sloc) / self.exec_sloc if self.exec_sloc else None
        )
        return result


def strip_comments(source: str) -> str:
    """Remove comments while preserving newlines and (roughly) string literals."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(source):
        c = source[i]
        n = source[i + 1] if i + 1 < len(source) else ""
        if block_depth:
            if c == "/" and n == "*":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif c == "*" and n == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            out.append(" " if c != "\n" else "\n")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        elif c == "/" and n == "*":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif c == "/" and n == "/":
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def category(path: Path, source_root: Path) -> str:
    rel = path.relative_to(source_root)
    return rel.parts[0] if len(rel.parts) > 1 else "library_root"


def classify_file(path: Path, source_root: Path) -> Stats:
    cleaned = strip_comments(path.read_text())
    result = Stats(category(path, source_root), modules=1)
    result.spec_fns = len(SPEC_FN.findall(cleaned))
    result.proof_fns = len(PROOF_FN.findall(cleaned))
    # Exclude proof/spec signatures from ordinary function count.
    result.exec_fns = max(0, len(EXEC_FN.findall(cleaned)) - result.spec_fns - result.proof_fns)
    result.format_types = len(
        re.findall(r"\b(?:struct|enum|type)\s+[A-Za-z_][A-Za-z0-9_]*Fmt\b", cleaned)
    )
    result.spec_parser_impls = len(re.findall(r"\bSpecParser\s+for\b", cleaned))
    result.parser_impls = len(re.findall(r"\bParser\s*<[^;{]*?\bfor\b", cleaned, re.S))
    result.serializer_impls = len(re.findall(r"\bSerializer\s*<[^;{]*?\bfor\b", cleaned, re.S))

    depth = 0
    contexts: list[tuple[int, str]] = []
    pending: str | None = None
    counts: Counter[str] = Counter()

    for line in cleaned.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        result.total_sloc += 1

        mode: str | None = None
        if PROOF_FN.search(line) or PROOF_BLOCK.search(line):
            mode = "proof"
        elif SPEC_FN.search(line):
            mode = "spec"
        elif EXEC_FN.search(line):
            mode = "exec"
        elif CONTRACT.search(line):
            mode = "spec"
        elif pending is not None:
            mode = pending
        elif contexts:
            mode = contexts[-1][1]

        counts[mode or "shared"] += 1

        opens = line.count("{")
        closes = line.count("}")
        starts_context = mode is not None and (
            PROOF_FN.search(line)
            or SPEC_FN.search(line)
            or EXEC_FN.search(line)
            or PROOF_BLOCK.search(line)
            or pending is not None
        )
        if starts_context and opens:
            contexts.append((depth, mode))
            pending = None
        elif mode is not None and (
            PROOF_FN.search(line) or SPEC_FN.search(line) or EXEC_FN.search(line)
        ) and not stripped.endswith(";"):
            pending = mode

        depth += opens - closes
        while contexts and depth <= contexts[-1][0]:
            contexts.pop()
        if pending is not None and stripped.endswith(";"):
            pending = None

    result.spec_sloc = counts["spec"]
    result.proof_sloc = counts["proof"]
    result.exec_sloc = counts["exec"]
    result.shared_sloc = counts["shared"]
    assert result.total_sloc == sum(counts.values())
    return result


def tracked_rs_files(repo: Path) -> list[Path]:
    output = subprocess.check_output(
        ["git", "ls-files", "vest_lib2/src"], cwd=repo, text=True
    )
    return sorted(repo / p for p in output.splitlines() if p.endswith(".rs"))


def markdown(rows: list[dict[str, object]]) -> str:
    lines = [
        "# VPS backend source and proof burden",
        "",
        "Ratios use nonblank, non-comment SLOC. P/C = (Spec + Proof) / Exec.",
        "",
        "| Area | Modules | SLOC | Spec | Proof | Exec | Shared | P/C Ratio | Formats |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for r in rows:
        ratio = "–" if r["proof_to_code"] is None else f'{r["proof_to_code"]:.2f}'
        lines.append(
            f'| {r["category"]} | {r["modules"]} | {r["total_sloc"]} | '
            f'{r["spec_sloc"]} | {r["proof_sloc"]} | {r["exec_sloc"]} | '
            f'{r["shared_sloc"]} | {ratio} | {r["format_types"]} |'
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    here = Path(__file__).resolve()
    default_repo = here.parents[2]
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=default_repo)
    parser.add_argument("--output-dir", type=Path, default=here.parents[1] / "results" / "derived")
    args = parser.parse_args()
    repo = args.repo.resolve()
    source_root = repo / "vest_lib2" / "src"

    grouped: dict[str, Stats] = {}
    total = Stats("TOTAL")
    for path in tracked_rs_files(repo):
        stats = classify_file(path, source_root)
        grouped.setdefault(stats.category, Stats(stats.category)).add(stats)
        total.add(stats)

    order = ["core", "combinators", "primitives", "asn1", "cbor", "library_root"]
    stats_rows = [grouped[k].row() for k in order if k in grouped] + [total.row()]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "backend_loc.json").write_text(json.dumps(stats_rows, indent=2) + "\n")
    with (args.output_dir / "backend_loc.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=stats_rows[0].keys())
        writer.writeheader()
        writer.writerows(stats_rows)
    (args.output_dir / "backend_loc.md").write_text(markdown(stats_rows))
    print(markdown(stats_rows), end="")


if __name__ == "__main__":
    main()

