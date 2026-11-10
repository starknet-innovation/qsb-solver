import json
import pathlib
import sys
import unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/sha-rotate-add'))
from trace_source import instrument, TRACE, CANDIDATE_TREE, CANDIDATE_GPUHASH


class TraceTests(unittest.TestCase):
    def test_only_the_frozen_tree_is_instrumented(self):
        source=ROOT/'research/optimized-subset/subset/tests/gpu_epochs/tree.cu'
        original=source.read_bytes();text=original.decode()
        traced=instrument(text)
        self.assertEqual(traced.replace(TRACE,''),text)
        self.assertEqual(traced.count('TRACE_SUB indices='),1)
        for changed in (traced,text+'\n'):
            with self.assertRaises(ValueError):instrument(changed)
        self.assertEqual(source.read_bytes(),original)

    def test_identities_match_the_locks(self):
        production=json.loads((ROOT/'worker/optimized/source-lock.json').read_text())
        experiment=json.loads((ROOT/'experiments/sha-rotate-add/experiment-lock.json').read_text())
        self.assertEqual(production['files']['subset/tests/gpu_epochs/tree.cu'],CANDIDATE_TREE)
        self.assertEqual(experiment['patchedGpuHashSha256'],CANDIDATE_GPUHASH)

    def test_published_native_trace_is_the_one_the_cpu_summary_verified(self):
        import hashlib
        evidence=ROOT/'experiments/sha-rotate-add/evidence'
        raw=(evidence/'native-trace.json').read_bytes();summary=json.loads((evidence/'native-trace-cpu.json').read_text())
        self.assertEqual(hashlib.sha256(raw).hexdigest(),summary['nativeResultSha256'])
        native=json.loads(raw)
        self.assertEqual((native['status'],len(native['ranges']),native['candidateSha256']),('native-completed-awaiting-cpu-verification',20,summary['candidateSha256']))
        self.assertNotIn('uuid',raw.decode().lower())
