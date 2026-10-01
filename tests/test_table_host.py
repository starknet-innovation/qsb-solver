"""Exercise host failure collection without Docker, CUDA or cloud access."""
import base64
import gzip
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]


class TableHostTests(unittest.TestCase):
    def run_host(self, fail):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            gate = root / "gate"
            gate.mkdir()
            (gate / "SHA256SUMS").write_text("")
            marker = root / "armed"
            marker.touch()
            results = root / "results"
            binaries = root / "bin"
            binaries.mkdir()
            commands = {
                "systemctl": "exit 0",
                "sha256sum": "exit 0",
                "nvidia-smi": 'if [ "$FAIL" = gpu ]; then exit 19; fi; echo mock-gpu',
                "docker": '''case "$1" in
pull) echo pull-log; [ "$FAIL" != pull ] || exit 17;;
run) echo gate-log; [ "$FAIL" != run ] || exit 42;;
rm) echo cleanup-log;;
esac''',
            }
            for name, body in commands.items():
                path = binaries / name
                path.write_text("#!/bin/bash\n" + body + "\n")
                path.chmod(0o755)
            script = (ROOT / "experiments/exact-table-batch/host.sh").read_text()
            script = script.replace("/opt/qsb-a10g-gate", str(gate))
            script = script.replace("/var/tmp/qsb-a10g-results", str(results))
            script = script.replace("/run/qsb-shutdown-armed", str(marker))
            host = root / "host.sh"
            host.write_text(script)
            env = dict(os.environ, FAIL=fail, PATH=str(binaries) + ":" + os.environ["PATH"])
            process = subprocess.run(
                ["bash", str(host), "ghcr.io/starknet-innovation/qsb-solver@sha256:" + "a" * 64,
                 str(int(time.time()) + 3600)], env=env, capture_output=True, text=True, timeout=20)
            envelope = json.loads(gzip.decompress(base64.b64decode((results / "public-result.b64").read_bytes())))
            self.assertIn("QSB_PUBLIC_RESULT_META=", process.stdout)
            self.assertEqual(envelope["exit-code.txt"].strip(), str(process.returncode))
            return process.returncode, envelope

    def test_pull_failure_preserved(self):
        code, files = self.run_host("pull")
        self.assertEqual(code, 17)
        self.assertIn("pull-log", files["pull.log"])
        self.assertNotIn("gate.log", files)

    def test_gpu_query_failure_preserved(self):
        code, files = self.run_host("gpu")
        self.assertEqual(code, 19)
        self.assertNotIn("gate.log", files)

    def test_workload_failure_preserved(self):
        code, files = self.run_host("run")
        self.assertEqual(code, 42)
        self.assertIn("gate-log", files["gate.log"])

    def test_success_collected(self):
        code, files = self.run_host("")
        self.assertEqual(code, 0)
        self.assertEqual(files["cleanup-exit-code.txt"].strip(), "0")


if __name__ == "__main__":
    unittest.main()
