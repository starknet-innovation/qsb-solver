import copy
import importlib.util
import json
from pathlib import Path
import unittest

PATH = Path(__file__).resolve().parents[1] / "experiments/exact-table-batch/verify_results.py"
SPEC = importlib.util.spec_from_file_location("table_results", PATH)
m = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)
SHA = "a" * 64
IMAGE = "ghcr.io/starknet-innovation/qsb-solver@sha256:" + "b" * 64


def fixture():
    files = {"exit-code.txt": "0\n", "runtime.txt": IMAGE,
             "binary.sha256": SHA + "  table-gate\n", "gpu.txt": "NVIDIA A10G, GPU-private-id, driver\n", "gate.log": ""}
    for name in m.TOOLS:
        row = dict(m.COUNTS, status="passed", gpu="NVIDIA A10G", table_sha256=[SHA] * 3,
                   timingExecuted=name == "normal", samples=[])
        if name == "normal":
            row["samples"] = [dict(pair=i // 2, order=i % 2,
                                    binary="candidate" if (i // 2 + i % 2) % 2 else "baseline",
                                    kernel_ms=1.0, construction_ms=2.0) for i in range(14)]
        files[name + ".json"] = json.dumps(row)
        log = m.COMPLETE + "\n"
        if name != "normal":
            log = "========= COMPUTE-SANITIZER\n" + log
            log += ("========= RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)\n"
                    if name == "racecheck" else "========= ERROR SUMMARY: 0 errors\n")
        files[name + ".log"] = log
    return files


class TableResultsTests(unittest.TestCase):
    def test_complete_receipt_reports_only_table_metrics(self):
        result = m.validate(fixture(), SHA, IMAGE, 0)
        self.assertFalse(result["solverSpeedupEstablished"])
        self.assertEqual(result["pairedTimeRatios"]["kernel_ms"]["median"], 1)

    def test_failure_and_identity_mismatch_rejected(self):
        for key, value in [("exit-code.txt", "42"), ("runtime.txt", "other"),
                           ("binary.sha256", "wrong"), ("gpu.txt", "NVIDIA Other")]:
            with self.subTest(key=key):
                files = fixture(); files[key] = value
                with self.assertRaises(ValueError): m.validate(files, SHA, IMAGE, 0)
        with self.assertRaises(ValueError): m.validate(fixture(), SHA, IMAGE, 42)

    def test_bad_sanitizer_or_missing_completion_rejected(self):
        for name in m.TOOLS:
            files = fixture(); files[name + ".log"] = ""
            with self.assertRaises(ValueError): m.validate(files, SHA, IMAGE, 0)
        files = fixture(); files["racecheck.log"] = files["racecheck.log"].replace("0 warnings", "1 warnings")
        with self.assertRaises(ValueError): m.validate(files, SHA, IMAGE, 0)

    def test_incomplete_or_inconsistent_json_rejected(self):
        original = fixture()
        for key, value in [("geometry", True), ("samples", []), ("timingExecuted", 1),
                           ("table_sha256", ["b" * 64] * 3)]:
            files = copy.deepcopy(original)
            row = json.loads(files["normal.json"]); row[key] = value
            files["normal.json"] = json.dumps(row)
            with self.assertRaises(ValueError): m.validate(files, SHA, IMAGE, 0)
        for text in ['{"a":1,"a":2}', '{"a":NaN}', '{"a":Infinity}', '{"status":"passed",']:
            with self.assertRaises(ValueError): m.strict_json(text)

    def test_unpinned_image_and_extreme_ratios_rejected(self):
        files = fixture(); files["runtime.txt"] = "latest"
        with self.assertRaises(ValueError): m.validate(files, SHA, "latest", 0)
        for baseline, candidate in [(1e-308, 1e308), (1e308, 1e-308)]:
            files = fixture(); row = json.loads(files["normal.json"])
            row["samples"][0]["kernel_ms"] = baseline
            row["samples"][1]["kernel_ms"] = candidate
            files["normal.json"] = json.dumps(row)
            with self.assertRaises(ValueError): m.validate(files, SHA, IMAGE, 0)

    def test_missing_pair_or_invalid_timing_rejected(self):
        for key, value in [("pair", 6), ("binary", "candidate"), ("kernel_ms", 0),
                           ("construction_ms", True), ("kernel_ms", float("nan"))]:
            files = fixture(); row = json.loads(files["normal.json"])
            row["samples"][0][key] = value; files["normal.json"] = json.dumps(row)
            with self.assertRaises(ValueError): m.validate(files, SHA, IMAGE, 0)


if __name__ == "__main__": unittest.main()
