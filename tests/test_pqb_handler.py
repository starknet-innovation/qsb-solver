"""The PQB worker handler: request and problem validation, and one unit end to end on the
CPU-emulated grinder. No GPU, network or credentials."""
import base64
import hashlib
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
sys.path.insert(0, str(ROOT / 'worker/pqb'))
import pqb_emulation as emu  # noqa: E402
import pqb_handler as handler  # noqa: E402
import pqb_ranges as ranges  # noqa: E402

COMMIT = 'ab' * 20
BINARY = emu.build()
STAGES = {'pinning': 'pin', 'round0': 'round0', 'round1': 'round1'}


def request(stage, raw, attempt=0, **changes):
    data = {'protocol': 'pqb-v1', 'stage': stage, 'attempt': attempt, 'searchVersion': 'pqb-ranked-v2',
            'problemBase64': base64.b64encode(raw).decode(), 'problemSha256': hashlib.sha256(raw).hexdigest(),
            'manifestHash': 'cd' * 32, 'kernelCommit': COMMIT}
    data.update(changes)
    return data


class ProblemValidationTest(unittest.TestCase):
    def test_fixture_problems_have_their_stage_shape(self):
        for stage, name in STAGES.items():
            raw = emu.problem(name, gate_bits=24)
            handler.parse_problem(raw, stage)
            _raw, unit = handler.validate_request(request(stage, raw), COMMIT)
            self.assertEqual(unit, ranges.work_range(stage, 0))
            for other in STAGES:
                if other != stage:
                    with self.assertRaises(ValueError):
                        handler.parse_problem(raw, other)

    def test_malformed_problems_are_refused(self):
        raw = emu.problem('round0', gate_bits=24)
        pin = emu.problem('pin', gate_bits=24)
        bad = [emu.problem('round0'),                                   # not the contract gate
               raw.replace(b'gate_tag 807207424', b'gate_tag 807207425'),
               raw + b'seed 00\n', raw + b'slot 109 99999\n', raw[:-1],
               raw.replace(b'K 16\n', b'K 16\nK 16\n'),
               raw.replace(b'slot 5 ', b'slot 05 '),
               raw.replace(b'n_slots 109', b'n_slots 108'),
               raw.replace(b'slot_len 10', b'slot_len 0'),
               raw.replace(b'preimage_len 4996', b'preimage_len 4995'),
               raw.replace(b'\npreimage ', b'\npreimage 0'),
               b'\n'.join(ln for ln in raw.split(b'\n') if not ln.startswith(b'C 3 1 ')),
               b'\n'.join(ln for ln in raw.split(b'\n') if not ln.startswith(b'B ')),
               raw.replace(b'\nB ', b'\nB  '), raw.replace(b'kind round', b'kind round\r'),
               raw.replace(b'slot 1 406', b'slot 1 380')]
        for i, case in enumerate(bad):
            with self.subTest(case=i), self.assertRaises(ValueError):
                handler.parse_problem(case, 'round0')
        for case in (pin.replace(b'seq_off', b'lt_off'), pin + b'slot 0 10\n', pin + b't 8\n'):
            with self.assertRaises(ValueError):
                handler.parse_problem(case, 'pinning')

    def test_requests_are_strict(self):
        raw = emu.problem('pin', gate_bits=24)
        good = request('pinning', raw)
        handler.validate_request(good, COMMIT)
        bad = [dict(good, seed='00'), {k: v for k, v in good.items() if k != 'attempt'},
               dict(good, protocol='qsb-config-a-v1'), dict(good, searchVersion='ranked-v2'),
               dict(good, kernelCommit='00' * 20), dict(good, stage='round2'), dict(good, stage='round0'),
               dict(good, attempt=-1), dict(good, attempt='0'), dict(good, attempt=ranges.unit_count('pinning')),
               dict(good, problemSha256='00' * 32), dict(good, manifestHash='zz'),
               dict(good, problemBase64=good['problemBase64'] + '!')]
        for i, case in enumerate(bad):
            with self.subTest(case=i), self.assertRaises((ValueError, TypeError)):
                handler.validate_request(case, COMMIT)

    def test_a_completion_line_must_describe_the_unit(self):
        unit = ranges.work_range('round0', 1)
        line = {'kind': 'round', 'prefix_start': int(unit['prefixStart']), 'prefix_count': unit['prefixCount'],
                'subset_start': int(unit['start']), 'zblocks': unit['count'], 'expected': unit['count'],
                'hits': 0, 'der_filter': 1, 'gate_hits': 5, 'complete': True}
        log = lambda d: 'x\n@range %s\n@done {}\n' % json.dumps(d)  # noqa: E731
        self.assertIsNotNone(handler.range_report(log(line), 'round0', unit))
        for change in ({'complete': False}, {'der_filter': 0}, {'zblocks': unit['count'] - 1},
                       {'prefix_start': 0}, {'subset_start': 0}, {'kind': 'pin'}, {'hits': None}):
            self.assertIsNone(handler.range_report(log(dict(line, **change)), 'round0', unit))
        self.assertIsNone(handler.range_report('', 'round0', unit))
        self.assertIsNone(handler.range_report(log(line) + log(line), 'round0', unit))


@unittest.skipUnless(BINARY, 'no C++ compiler')
class HandlerOnEmulationTest(unittest.TestCase):
    """Full units are far too large for emulation, so these patch in a small unit."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        shutil.copy(BINARY, self.root / 'grind')
        for name in ('pqb_handler.py', 'pqb_ranges.py'):
            shutil.copy(ROOT / 'worker/pqb' / name, self.root / name)
        self.bind()
        self.saved = handler.work_range

    def tearDown(self):
        handler.work_range = self.saved
        self.tmp.cleanup()

    def bind(self):
        files = {n: hashlib.sha256((self.root / n).read_bytes()).hexdigest() for n in handler.REQUIRED}
        (self.root / 'binding.json').write_text(json.dumps(
            {'format': 'qsb-pqb-candidate-v1', 'status': 'HOLD', 'solverCommit': COMMIT, 'files': files}))

    def small_unit(self, unit):
        handler.work_range = lambda stage, attempt: (self.saved(stage, attempt), unit)[1]

    def test_units_complete(self):
        self.small_unit({'version': 'pqb-ranked-v2', 'start': '0', 'count': 400, 'sequence': 0x80000000,
                         'sequenceCount': 2, 'locktime': 500000000, 'locktimeCount': 200})
        out = handler.handler({'input': request('pinning', emu.problem('pin', gate_bits=24))}, root=self.root)
        self.assertEqual((out['status'], out['checkpoint'], out['verified']), ('completed', 'range-complete', False))
        self.assertEqual((out['trials'], out['candidates'], out['kernelCommit']), (400 * 72, [], COMMIT))
        self.assertIsInstance(out['gateHits'], int)
        for stage, picks in (('round0', 192), ('round1', 64)):
            first = ranges.subset_rank_of_prefix(stage, 5)
            count = ranges.subset_rank_of_prefix(stage, 8) - first
            self.small_unit({'version': 'pqb-ranked-v2', 'start': str(first), 'count': count,
                             'prefixStart': '5', 'prefixCount': 3})
            out = handler.handler({'input': request(stage, emu.problem(stage, gate_bits=24))}, root=self.root)
            self.assertEqual(out['status'], 'completed', out)
            self.assertEqual(out['trials'], count * picks)

    def test_a_unit_the_grinder_does_not_account_for_is_not_credited(self):
        # the unit claims more z-blocks than its range holds: the completion line cannot match
        self.small_unit({'version': 'pqb-ranked-v2', 'start': '0', 'count': 401, 'sequence': 0x80000000,
                         'sequenceCount': 2, 'locktime': 500000000, 'locktimeCount': 200})
        out = handler.handler({'input': request('pinning', emu.problem('pin', gate_bits=24))}, root=self.root)
        self.assertEqual((out['status'], out['checkpoint']), ('failed', 'requires-verification-or-resume'))
        self.assertNotIn('gateHits', out)
        # a range the grinder refuses
        self.small_unit({'version': 'pqb-ranked-v2', 'start': '0', 'count': 2, 'sequence': 0xFFFFFFFD,
                         'sequenceCount': 2, 'locktime': 500000000, 'locktimeCount': 1})
        out = handler.handler({'input': request('pinning', emu.problem('pin', gate_bits=24))}, root=self.root)
        self.assertEqual(out['status'], 'failed')

    def test_an_interrupted_unit_is_not_credited(self):
        self.small_unit({'version': 'pqb-ranked-v2', 'start': '0', 'count': 14 * 1200000000,
                         'sequence': 0x80000000, 'sequenceCount': 14, 'locktime': 500000000,
                         'locktimeCount': 1200000000})
        out = handler.handler({'input': request('pinning', emu.problem('pin', gate_bits=24))},
                              root=self.root, timeout=1)
        self.assertEqual((out['status'], out['candidates']), ('interrupted', []))

    def test_a_grinder_that_exits_as_the_timeout_fires_is_still_interrupted(self):
        # the process group is already gone when the handler signals it
        import os
        from unittest import mock
        self.small_unit({'version': 'pqb-ranked-v2', 'start': '0', 'count': 14 * 1200000000,
                         'sequence': 0x80000000, 'sequenceCount': 14, 'locktime': 500000000,
                         'locktimeCount': 1200000000})
        real = os.killpg

        def gone(pid, sig):
            real(pid, 9)                                 # it dies...
            os.waitpid(pid, 0)                           # ...and is reaped before the signal lands
            raise ProcessLookupError()

        with mock.patch.object(handler.os, 'killpg', side_effect=gone):
            out = handler.handler({'input': request('pinning', emu.problem('pin', gate_bits=24))},
                                  root=self.root, timeout=1)
        self.assertEqual((out['status'], out['candidates'], out['checkpoint']),
                         ('interrupted', [], 'requires-verification-or-resume'))

    def test_installed_files_must_match_the_binding(self):
        event = {'input': request('pinning', emu.problem('pin', gate_bits=24))}
        with open(self.root / 'grind', 'ab') as f:
            f.write(b'\0')
        with self.assertRaises(ValueError):
            handler.handler(event, root=self.root)
        self.bind()
        binding = json.loads((self.root / 'binding.json').read_text())
        (self.root / 'binding.json').write_text(json.dumps(dict(binding, status='RELEASED')))
        with self.assertRaises(ValueError):
            handler.handler(event, root=self.root)


if __name__ == '__main__':
    unittest.main()
