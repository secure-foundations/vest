"""Regression tests for units, uncertainty, and run integrity."""

import contextlib
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import report
import common as run
import run as runner


class ReportingTests(unittest.TestCase):
    def measurement(self, impl, samples=(10.0, 10.0, 10.0), byte_count=2**20):
        return report.Measurement("flat/parse", impl, samples[1], min(samples), max(samples),
                                  0.95, byte_count, samples, 10)

    def test_throughput_units_and_ratio_orientation(self):
        vest = self.measurement("vest", (10.0, 10.0, 10.0))
        hand = self.measurement("hand", (20.0, 20.0, 20.0))
        self.assertEqual(vest.mib_per_second(10), 100_000_000)
        self.assertEqual(report.ratio_interval(vest, hand, 100), (2.0, 2.0, 2.0))
        with self.assertRaisesRegex(ValueError, "unequal byte"):
            report.ratio_interval(vest, self.measurement("hand", byte_count=1))

    def test_bootstrap_uncertainty_is_nonzero_and_reproducible(self):
        vest = self.measurement("vest", (8.0, 10.0, 12.0))
        hand = self.measurement("hand", (16.0, 20.0, 24.0))
        first = report.ratio_interval(vest, hand, 500)
        self.assertLess(first[1], first[0])
        self.assertGreater(first[2], first[0])
        self.assertEqual(first, report.ratio_interval(vest, hand, 500))

    def test_missing_throughput_still_reports_latency(self):
        vest = self.measurement("vest", byte_count=None)
        hand = self.measurement("hand", byte_count=None)
        table = report.markdown_tables([vest, hand], {}, set())
        self.assertIn("10.0 ns", table)
        self.assertIn("hand", table)
        self.assertIn("—", table)

    def test_job_matrix_covers_native_cbor4ii_but_not_broken_fragmented_parse(self):
        jobs = [identity for _, identity in run.jobs([])]
        self.assertEqual(len(jobs), len(set(jobs)))
        self.assertEqual(len(jobs), 99)
        self.assertIn("cbor/cose/parse/cbor4ii", jobs)
        self.assertNotIn("cbor/synthetic/parse/cbor4ii", jobs)

    def test_refuse_partial_and_stale_runs(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            manifest = {"policy": run.POLICY, "status": "running", "jobs": [], "measurements": [], "fingerprint": "old"}
            path = directory / "run.json"
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "did not complete"):
                report.load_run(directory)
            manifest["status"] = "complete"
            path.write_text(json.dumps(manifest))
            with patch("report.fingerprint", return_value="new"):
                with self.assertRaisesRegex(ValueError, "sources/corpora differ"):
                    report.load_run(directory)
                with contextlib.redirect_stderr(io.StringIO()) as stderr:
                    report.load_run(directory, allow_stale=True)
                self.assertIn("historical", stderr.getvalue())

    def test_hashes_detect_overwritten_measurements(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            sample_dir = directory / "flat_parse" / "vest" / "new"
            sample_dir.mkdir(parents=True)
            documents = {
                "benchmark.json": {"group_id": "flat/parse", "function_id": "vest", "throughput": {"Bytes": 100}},
                "estimates.json": {"median": {"point_estimate": 10, "confidence_interval": {
                    "lower_bound": 9, "upper_bound": 11, "confidence_level": 0.95}}},
                "sample.json": {"iters": [1, 2, 3], "times": [10, 20, 30]},
            }
            files = {}
            for name, data in documents.items():
                path = sample_dir / name
                path.write_text(json.dumps(data))
                files[str(path.relative_to(directory))] = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest = {"measurements": [{"id": "flat/parse/vest", "files": files, "corpus": {"items": 10, "bytes": 100}}],
                        "settings": {"samples": 3}}
            self.assertEqual(report.load_measurements(directory, manifest)[0].items, 10)
            (sample_dir / "sample.json").write_text("{}")
            with self.assertRaisesRegex(ValueError, "modified or stale"):
                report.load_measurements(directory, manifest)

    def test_external_inputs_are_rechecked_after_recording(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "blocks.txt"
            path.write_bytes(b"first corpus")
            with patch.dict("os.environ", {"VEST_BENCH_BITCOIN_CORPUS": str(path)}):
                recorded = run.external_corpus()
            self.assertTrue(run.external_corpus_matches(recorded))
            path.write_bytes(b"different corpus")
            self.assertFalse(run.external_corpus_matches(recorded))
            path.unlink()
            self.assertFalse(run.external_corpus_matches(recorded))

    def test_fingerprint_is_stable_when_deleted_index_entries_disappear(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            code = root / "vest_bench" / "code.rs"
            code.parent.mkdir()
            code.write_text("fn main() {}")
            with patch("common.ROOT", root):
                with patch("common.subprocess.check_output", return_value=b"vest_bench/deleted.rs\0vest_bench/code.rs\0"):
                    before = run.fingerprint()
                with patch("common.subprocess.check_output", return_value=b"vest_bench/code.rs\0"):
                    self.assertEqual(run.fingerprint(), before)
    def test_inventory_drift_is_not_silently_ignored(self):
        expected = run.jobs(["bitcoin"])
        listing = "\n".join(f"{identity}: benchmark" for _, identity in expected)
        with patch("common.subprocess.check_output", return_value=listing):
            run.validate_inventory({"bitcoin": "binary"}, {})
        with patch("common.subprocess.check_output", return_value=listing + "\nunregistered: benchmark"):
            with self.assertRaisesRegex(RuntimeError, "inventory changed"):
                run.validate_inventory({"bitcoin": "binary"}, {})

    def test_freshness_checks_reject_old_measurement_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "new"
            path.mkdir()
            (path / "benchmark.json").write_text(json.dumps({"group_id": "flat/parse", "function_id": "vest"}))
            with self.assertRaisesRegex(RuntimeError, "no fresh measurements"):
                runner.capture_estimate(Path(temporary), "flat/parse/vest", 0)

    def test_duplicate_measurements_and_partial_audits_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)
            manifest = {"policy": run.POLICY, "status": "complete", "jobs": ["a"],
                        "measurements": [{"id": "a"}, {"id": "a"}], "fingerprint": "unused"}
            (path / "run.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "duplicate measurements"):
                report.load_run(path)
            manifest.update(jobs=["a", "b"], measurements=[{"id": "a"}, {"id": "b"}], allocations={"a": {}})
            (path / "run.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "incomplete allocation"):
                report.load_run(path)


if __name__ == "__main__":
    unittest.main()
