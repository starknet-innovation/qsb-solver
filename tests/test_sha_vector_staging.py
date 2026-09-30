import hashlib
import importlib.util
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import zipfile

PATH=Path(__file__).resolve().parents[1]/'experiments/generic-sha-vector/stage_full.py'
spec=importlib.util.spec_from_file_location('stage_full',PATH)
stage=importlib.util.module_from_spec(spec);spec.loader.exec_module(stage)

class StagingTests(unittest.TestCase):
    def run_stage(self, corrupt=False, gate="trace"):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);archive=root/'input.zip';dest=root/'gate'
            public=b'public script';receipt=b'{}';binary=b'public binary'
            with zipfile.ZipFile(archive,'w') as z:
                for name in ('baseline','candidate','candidate-trace'):z.writestr(name,binary)
                z.writestr('candidate-trace.diff',b'diagnostic diff');z.writestr('trace-receipt.json',receipt)
            files={'tools/run_trace.py':{'url':'https://example.invalid/script','sha256':hashlib.sha256(public).hexdigest()},'bundle/fixtures.json':{'url':'https://example.invalid/fixture','sha256':hashlib.sha256(public).hexdigest()}}
            hashes={name:hashlib.sha256(binary).hexdigest() for name in ('baseline','candidate','candidate-trace')}
            if corrupt:hashes['candidate']='0'*64
            with patch.object(stage,'payload',return_value=files),patch.object(stage,'BINARIES',hashes),patch.object(stage,'ZIP_SHA',hashlib.sha256(archive.read_bytes()).hexdigest()):
                script=stage.render('a'*40,'https://example.invalid/archive','ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64,gate,hashlib.sha256(receipt).hexdigest())
            subprocess.run(['bash','-n'],input=script,text=True,check=True)
            code=script.split("python3 - <<'QSB_STAGE'\n",1)[1].split('\nQSB_STAGE',1)[0]
            code=code.replace('/var/tmp/qsb-frozen-pair.zip',str(archive)).replace('/opt/qsb-a10g-gate',str(dest))
            with patch('urllib.request.urlopen',side_effect=lambda *a,**k:io.BytesIO(public)):
                exec(compile(code,'generated-stage','exec'),{})
            self.assertEqual((dest/'bundle/candidate').read_bytes(),binary)
            self.assertTrue((dest/'SHA256SUMS').exists())

    def test_frozen_archive_and_file_checks(self):self.run_stage()
    def test_wrong_binary_rejects(self):
        with self.assertRaises(AssertionError):self.run_stage(True)
    def test_timing_handoff_shell_and_archive(self):self.run_stage(gate="timing")
    def test_moving_runtime_rejected(self):
        with self.assertRaises(ValueError):stage.render('a'*40,'https://example.invalid/x','image:latest','trace','b'*64)

if __name__=='__main__':unittest.main()
