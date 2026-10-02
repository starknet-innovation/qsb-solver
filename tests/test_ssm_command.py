import base64
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('ssm_command',ROOT/'ops/aws-gpu-execution/ssm_command.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class SsmCommandTests(unittest.TestCase):
    def test_bash_only_payload_runs_through_posix_shell(self):
        script="set -euo pipefail\nitems=(one two)\n[[ ${#items[@]} == 2 ]]\nprintf '%s\\n' \"${items[1]}\""
        p=subprocess.run(['/bin/sh','-c',m.bash_command(script)],text=True,capture_output=True)
        self.assertEqual(p.returncode,0,p.stderr);self.assertEqual(p.stdout,'two\n')
    def test_pipefail_and_exit_status_survive_wrapper(self):
        p=subprocess.run(['/bin/sh','-c',m.bash_command('set -euo pipefail\nfalse | true\necho SHOULD_NOT_RUN')],text=True,capture_output=True)
        self.assertNotEqual(p.returncode,0);self.assertNotIn('SHOULD_NOT_RUN',p.stdout)
    def test_outer_shell_does_not_expand_payload(self):
        script="set -euo pipefail\nprintf '%s\\n' '$HOME $(echo should-not-run) `echo neither`'"
        p=subprocess.run(['/bin/sh','-c',m.bash_command(script)],text=True,capture_output=True,check=True)
        self.assertEqual(p.stdout,'$HOME $(echo should-not-run) `echo neither`\n')
    def envelope(self,value):
        data=base64.b64encode(gzip.compress(json.dumps(value).encode()))
        return 'RESULT_SHA256='+hashlib.sha256(data).hexdigest()+'\nRESULT_BASE64='+data.decode()+'\n'
    def test_valid_result_and_missing_duplicate_corrupt_rejection(self):
        good=self.envelope({'exit-code.txt':'0','native.json':'{}'})
        self.assertEqual(m.decode_result(good)['exit-code.txt'],'0')
        for bad in ['', '/bin/sh: Illegal option -o pipefail', good+good,good.replace('RESULT_SHA256=','RESULT_SHA256=0'),self.envelope(['wrong schema'])]:
            with self.subTest(bad=bad[:50]),self.assertRaises(ValueError):m.decode_result(bad)
