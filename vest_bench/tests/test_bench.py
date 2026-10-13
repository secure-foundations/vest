"""Regression tests for benchmark selection, reporting, and provenance."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import bench


class BenchTests(unittest.TestCase):
    def measurement(self, name="Vest", samples=(10., 10., 10.), byte_count=2**20, items=10):
        return bench.Measurement(f"micro/bits/parse/{name}", samples[1], min(samples), max(samples),
                                 byte_count, items, samples)

    def fixture(self, directory):
        row = self.measurement()
        raw = directory / "criterion/bits/Vest/new"
        raw.mkdir(parents=True)
        documents = {
            "benchmark.json": {"group_id": "micro/bits/parse", "function_id": "Vest", "throughput": {"Bytes": row.bytes}},
            "sample.json": {"iters": [1, 2, 3], "times": [10, 20, 30]},
            "estimates.json": {"median": {"point_estimate": 10, "confidence_interval": {"lower_bound": 9, "upper_bound": 11}}},
        }
        for name, data in documents.items():
            (raw / name).write_text(json.dumps(data))
        manifest = {"version": bench.VERSION, "status": "complete", "fingerprint": "source", "dirty": False,
                    "quick": False, "targets": [], "started": "2026-10-12", "seed": 1234, "commit": "commit",
                    "rustc": "rustc test", "machine": {"cpu": "Test CPU", "ram_bytes": 2**30, "platform": "Test OS", "logical_cpus": 1},
                    "settings": {"samples": 100, "warmup_seconds": 3, "measurement_seconds": 5},
                    "jobs": [{"id": row.id, "items": row.items, "bytes": row.bytes}], "allocations": None,
                    "measurements": [{"id": row.id, "directory": str(raw.relative_to(directory / "criterion"))}]}
        bench.save(directory / "run.json", manifest)
        return manifest, raw

    def test_units_and_ratios(self):
        vest, hand = self.measurement(), self.measurement("hand", (20., 20., 20.))
        self.assertEqual(vest.rate(10), 100_000_000)
        self.assertEqual(bench.ratio(vest, hand), "2.00× [2.00–2.00]")
        variable = self.measurement("hand", (16., 20., 24.))
        ratio = bench.ratio(vest, variable)
        self.assertEqual(ratio, bench.ratio(vest, variable))
        self.assertNotEqual(ratio, "2.00× [2.00–2.00]")
        for different in (self.measurement(byte_count=1), self.measurement(items=1)):
            with self.assertRaisesRegex(ValueError, "unequal"):
                bench.ratio(vest, different)

    def test_component_prefixes(self):
        rows = [{"id": f"micro/{name}/parse/Vest"} for name in ("bits", "bits_extra")]
        self.assertEqual(bench.select(rows, ["micro/bits/", "micro/bits/parse"]), rows[:1])
        self.assertEqual(bench.select(rows, []), rows)
        with self.assertRaisesRegex(ValueError, "unknown target"):
            bench.select(rows, ["micro/bit"])

    def test_workload_listing_uses_input_sizes(self):
        entries = [{"id": f"bitcoin/blocks/{op}/{name}", "items": 4, "bytes": 6517345}
                   for op in ("parse", "serialize") for name in ("Vest", "rust-bitcoin")]
        self.assertEqual(bench.workload_list(entries, []), "bitcoin/blocks  4 items  6517345 bytes")
        entries += [{"id": f"cbor/synthetic/{op}/Vest", "items": 1536, "bytes": size}
                    for op, size in (("parse", 109120), ("serialize", 62985))]
        self.assertEqual(bench.workload_list(entries, ["cbor/synthetic/serialize"]),
                         "cbor/synthetic  1536 items  109120 bytes")

    @patch("bench.fingerprint", return_value="source")
    def test_load_and_capture(self, _):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            manifest, raw = self.fixture(directory)
            _, rows = bench.load_run(directory)
            self.assertEqual(rows[0].samples, (10, 10, 10))
            self.assertEqual(bench.capture(directory / "criterion", rows[0].id), manifest["measurements"][0])
            with self.assertRaisesRegex(ValueError, "found 0"):
                bench.capture(directory / "criterion", "absent")
            for invalid in (dict(manifest, version=0), dict(manifest, status="running"),
                            dict(manifest, measurements=[]), dict(manifest, jobs=manifest["jobs"] * 2),
                            dict(manifest, measurements=manifest["measurements"] * 2), dict(manifest, allocations={})):
                bench.save(directory / "run.json", invalid)
                with self.assertRaises(ValueError):
                    bench.load_run(directory)
            bench.save(directory / "run.json", dict(manifest, fingerprint="old"))
            with self.assertRaisesRegex(ValueError, "sources/corpora differ; rerun benchmarks"):
                bench.load_run(directory)
            bench.save(directory / "run.json", manifest)
            manifest["measurements"][0]["directory"] = "../escape"
            bench.save(directory / "run.json", manifest)
            with self.assertRaisesRegex(ValueError, "escapes"):
                bench.load_run(directory)
            manifest["measurements"][0]["directory"] = str(raw.relative_to(directory / "criterion"))
            bench.save(directory / "run.json", manifest)
            (raw / "benchmark.json").write_text(json.dumps({"group_id": "wrong", "function_id": "Vest"}))
            with self.assertRaisesRegex(ValueError, "mismatch"):
                bench.load_run(directory)

    def test_single_latest_pointer(self):
        with tempfile.TemporaryDirectory() as temporary, patch("bench.RESULTS", Path(temporary)):
            root = Path(temporary)
            for name, targets, quick in (("full", [], False), ("subset", ["tls"], False), ("quick", [], True)):
                directory = root / "runs" / name
                directory.mkdir(parents=True)
                bench.publish(directory, {"status": "complete", "targets": targets, "quick": quick})
            self.assertEqual(json.loads((root / "latest.json").read_text()), {"run": "runs/full"})
            self.assertEqual(len(list(root.glob("latest*.json"))), 1)
            with self.assertRaisesRegex(ValueError, "incomplete"):
                bench.publish(directory, {"status": "failed"})

    @patch("bench.fingerprint", return_value="source")
    def test_tables_and_joint_publication(self, _):
        with tempfile.TemporaryDirectory() as temporary, patch("bench.ROOT", Path(temporary)):
            root = Path(temporary)
            manifest, _ = self.fixture(root)
            rows = [self.measurement(), self.measurement("hand", (20., 20., 20.))]
            table = bench.tables(rows, compact=True)
            self.assertEqual(table.count("### Microformats"), 1)
            self.assertIn("#### Parse", table)
            self.assertNotIn("µs", table)
            rendered = bench.render(manifest, rows, root)
            self.assertIn("| CPU | Test CPU |", rendered)
            self.assertNotIn("{'", rendered)
            counts = dict(allocations=0, reallocations=0, requested_bytes=0, deallocations=0)
            manifest["allocations"] = {row.id: counts for row in rows}
            self.assertNotIn(rows[1].id, bench.render(manifest, rows[:1], root))
            readme = root / "vest_bench/README.md"
            readme.parent.mkdir()
            (readme.parent / "results").mkdir()
            readme.write_text(f"Before\n{bench.BEGIN}\nold\n{bench.END}\nAfter")
            bench.write_reports(root, manifest, rows)
            self.assertIn(table, readme.read_text())
            self.assertIn(bench.tables(rows), (readme.parent / "results/2026-10-12.md").read_text())
            self.assertTrue(readme.read_text().endswith("After"))
            self.assertIn("Auto-generated", (readme.parent / "results/2026-10-12.md").read_text())
            bench.write_reports(root, dict(manifest, dirty=True), rows)
            self.assertIn("| Uncommitted files | Yes |", readme.read_text())
            for change in ({"quick": True}, {"targets": ["micro"]}, {"fingerprint": "old"},
                           {"machine": dict(manifest["machine"], ram_bytes=None)}):
                with self.assertRaisesRegex(ValueError, "current-source"):
                    bench.write_reports(root, dict(manifest, **change), rows)


if __name__ == "__main__":
    unittest.main()
