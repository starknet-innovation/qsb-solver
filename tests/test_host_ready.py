"""Readiness ordering/timeout checks without a live host or provider."""
from pathlib import Path
import subprocess
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Ready(unittest.TestCase):
    def run_ready(self, marker, now, deadline):
        script=(ROOT/'ops/aws-gpu-execution/ready.sh').read_text()
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)
            script=script.replace('/run/qsb-shutdown-armed',str(path/'marker'))
            script=script.replace('systemctl is-active --quiet qsb-benchmark-expire.timer','true').replace('systemctl is-active --quiet cloud-final.service','true')
            script=script.replace('sleep 2','touch '+str(path/'marker'))
            script=script.replace('$(date -u +%s)',str(now))
            if marker:(path/'marker').touch()
            return subprocess.run(['bash','-c',script,'test',str(deadline)],capture_output=True,text=True,timeout=2)
    def test_waits_for_marker_after_ssm_is_online(self):
        p=self.run_ready(False,1790000000,1790001500)
        self.assertEqual(p.returncode,0,p.stderr);self.assertIn('QSB_HOST_READY',p.stdout)
    def test_rejects_insufficient_remaining_time(self):
        self.assertEqual(self.run_ready(True,1790000000,1790001000).returncode,2)
    def test_rejects_malformed_deadline(self):
        self.assertNotEqual(self.run_ready(True,1790000000,'bad').returncode,0)
