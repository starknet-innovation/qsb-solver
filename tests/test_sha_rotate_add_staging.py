import hashlib
import importlib.util
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import zipfile

PATH=Path(__file__).resolve().parents[1]/'experiments/sha-rotate-add/stage_full.py'
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
    def test_unfrozen_identities_refuse(self):
        arguments=('a'*40,'https://example.invalid/x','ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64,'trace','b'*64)
        with patch.object(stage,'ZIP_SHA',None),self.assertRaisesRegex(ValueError,'not frozen'):stage.render(*arguments)
        with patch.object(stage,'BINARIES',{**stage.BINARIES,'candidate-trace':None}),self.assertRaisesRegex(ValueError,'not frozen'):stage.render('a'*40,'https://example.invalid/x','ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64,'trace','b'*64)
    def test_command_line_writes_template_and_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);url=root/'url.txt';url.write_text('https://example.invalid/archive\n');out=root/'host-template.sh'
            argv=['stage_full.py','a'*40,str(url),'ghcr.io/starknet-innovation/qsb-solver@sha256:'+'b'*64,'trace','b'*64,str(out)]
            import runpy
            with patch('sys.argv',argv),patch('subprocess.check_output',return_value=b'public bytes'):
                runpy.run_path(str(PATH),run_name='__main__')
            self.assertEqual((root/'host-template.sh.sha256').read_text().strip(),hashlib.sha256(out.read_bytes()).hexdigest())
            with patch('sys.argv',argv),patch('subprocess.check_output',return_value=b'public bytes'),self.assertRaises(FileExistsError):
                runpy.run_path(str(PATH),run_name='__main__')
    def test_moving_runtime_rejected(self):
        with self.assertRaises(ValueError):stage.render('a'*40,'https://example.invalid/x','image:latest','trace','b'*64)

if __name__=='__main__':unittest.main()
