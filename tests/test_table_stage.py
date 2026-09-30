"""Offline ZIP and generated-handoff checks; never run the staged gate."""
import hashlib
import importlib.util
import io
from pathlib import Path
import stat
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import warnings
import zipfile

PATH = Path(__file__).resolve().parents[1] / "experiments/exact-table-batch/stage.py"
SPEC = importlib.util.spec_from_file_location("table_stage", PATH)
m = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)
BINARY = b"table-only test bytes; never executed"
BINARY_SHA = hashlib.sha256(BINARY).hexdigest()
COMMIT = "a" * 40
IMAGE = "ghcr.io/starknet-innovation/qsb-solver@sha256:" + "b" * 64


def archive(entries=None):
    stream = io.BytesIO()
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", UserWarning)
        with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED) as bundle:
            for name, data in entries or [("table-gate", BINARY), ("source.cu", b"source")]:
                bundle.writestr(name, data)
    return stream.getvalue()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class TableStageTests(unittest.TestCase):
    def test_exact_entry_only_and_exclusive_output(self):
        raw = archive()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            zipped = root / "artifact.zip"
            zipped.write_bytes(raw)
            output = root / "table-gate"
            self.assertEqual(m.validate_archive(zipped, sha(raw), BINARY_SHA), BINARY)
            m.extract_table_gate(zipped, output, sha(raw), BINARY_SHA)
            self.assertEqual(output.read_bytes(), BINARY)
            self.assertEqual(output.stat().st_mode & 0o777, 0o755)
            self.assertEqual({p.name for p in root.iterdir()}, {"artifact.zip", "table-gate"})
            with self.assertRaises(FileExistsError):
                m.extract_table_gate(zipped, output, sha(raw), BINARY_SHA)
            self.assertEqual(output.read_bytes(), BINARY)
            self.assertEqual(zipped.read_bytes(), raw)

    def test_digests_and_mutated_archive_fail_before_output(self):
        raw = archive()
        cases = [(raw + b"mutation", sha(raw), BINARY_SHA),
                 (raw, "c" * 64, BINARY_SHA), (raw, sha(raw), "d" * 64),
                 (archive([("table-gate", BINARY + b"changed")]), None, BINARY_SHA)]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "table-gate"
            for data, zip_sha, binary_sha in cases:
                with self.subTest(zip_sha=zip_sha, binary_sha=binary_sha):
                    with self.assertRaises(ValueError):
                        m.extract_table_gate(data, output, zip_sha or sha(data), binary_sha)
                    self.assertFalse(output.exists())

    def test_duplicates_symlinks_and_unsafe_paths_rejected(self):
        link = zipfile.ZipInfo("unselected-link")
        link.create_system = 3
        link.external_attr = (stat.S_IFLNK | 0o777) << 16
        cases = [[("table-gate", BINARY), ("table-gate", BINARY)],
                 [("table-gate", BINARY), (link, b"table-gate")]]
        for name in ("../escape", "/absolute", "nested/../escape", "nested\\escape", "./other"):
            cases.append([("table-gate", BINARY), (name, b"other")])
        for entries in cases:
            raw = archive(entries)
            with self.subTest(entries=str(entries)):
                with self.assertRaises(ValueError):
                    m.validate_archive(raw, sha(raw), BINARY_SHA)

    def test_missing_exact_entry_and_size_limits(self):
        nested = archive([("nested/table-gate", BINARY)])
        with self.assertRaisesRegex(ValueError, "missing exact"):
            m.validate_archive(nested, sha(nested), BINARY_SHA)
        raw = archive()
        for name, limit in (("MAX_ARCHIVE", len(raw) - 1),
                            ("MAX_MEMBER", len(BINARY) - 1), ("MAX_TOTAL", len(BINARY))):
            with self.subTest(limit=name), patch.object(m, name, limit):
                with self.assertRaises(ValueError):
                    m.validate_archive(raw, sha(raw), BINARY_SHA)

    def test_render_is_bounded_and_table_only(self):
        sources = {"host.sh": {"sha256": "c" * 64, "url": "https://example.invalid/host.sh"},
                   "ready.sh": {"sha256": "d" * 64, "url": "https://example.invalid/ready.sh"}}
        with patch.object(m, "payload", return_value=sources):
            script = m.render(COMMIT, "https://example.invalid/artifact.zip?sig=abc&more=def",
                              "e" * 64, BINARY_SHA, IMAGE)
        self.assertLessEqual(len(script.encode()), 60000)
        self.assertEqual(script.count("__DEADLINE__"), 1)
        self.assertIn("--kill-after=5s 180 python3", script)
        self.assertIn("MAX_ARCHIVE,120", script)
        self.assertIn("--proto-redir", script)
        self.assertIn("extract_table_gate(archive,root/'table-gate'", script)
        self.assertLess(script.index("bash /opt/qsb-a10g-gate/ready.sh"),
                        script.index("bash /opt/qsb-a10g-gate/host.sh"))
        self.assertNotIn("host-full", script)
        self.assertNotIn("Authorization", script)
        subprocess.run(["bash", "-n"], input=script, text=True, check=True, capture_output=True)
        python = script.split("<<'QSB_TABLE_STAGE'\n", 1)[1].split("\nQSB_TABLE_STAGE\n", 1)[0]
        compile(python, "generated-stage", "exec")

    def test_payload_binds_only_committed_sources(self):
        contents = (b"commit\n", b"#!/bin/bash\necho host\n", b"#!/bin/bash\necho ready\n")
        with patch.object(m.subprocess, "check_output", side_effect=contents) as call:
            sources = m.payload(COMMIT)
        self.assertEqual(set(sources), {"host.sh", "ready.sh"})
        for name, raw in zip(("host.sh", "ready.sh"), contents[1:]):
            self.assertEqual(sources[name]["sha256"], sha(raw))
            self.assertEqual(sources[name]["url"],
                             "https://raw.githubusercontent.com/starknet-innovation/qsb-solver/" + COMMIT + "/" + m.SOURCES[name])
        self.assertEqual(call.call_args_list[1].args[0],
                         ["git", "show", COMMIT + ":experiments/exact-table-batch/host.sh"])
        with self.assertRaises(ValueError):
            m.payload("main")

    def test_invalid_inputs_rejected_before_payload(self):
        valid = [COMMIT, "https://example.invalid/artifact.zip", "c" * 64, BINARY_SHA, IMAGE]
        for index, value in ((1, "http://example.invalid/artifact.zip"), (1, "https://x\ncommand"),
                             (2, "bad"), (3, "bad"), (4, "image:latest")):
            args = valid.copy()
            args[index] = value
            with patch.object(m, "payload") as call, self.assertRaises(ValueError):
                m.render(*args)
            call.assert_not_called()


if __name__ == "__main__":
    unittest.main()
