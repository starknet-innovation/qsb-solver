"""Public exporter layout vs independent full-transaction vectors; no native GPU claim."""
import hashlib
import json
from pathlib import Path
import struct
import unittest

ROOT = Path(__file__).resolve().parent / 'fixtures/cmsverify-v1'


def load(name):
    return json.loads((ROOT / name).read_text())


class CorrectedFixturesTests(unittest.TestCase):
    def test_file_integrity_and_public_state(self):
        provenance = load('provenance.json')
        for name, digest in provenance['files'].items():
            self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), digest)
        state = load('public-state.json')
        self.assertNotIn('hors_secrets', state)
        self.assertTrue(all(set(r) == {'r', 's', 'sig'} for r in state['round_sigs']))
        self.assertEqual(state['scriptVersion'], provenance['scriptVersion'])
        # Decode opcodes rather than count arbitrary signature/push bytes.
        raw = bytes.fromhex(state['full_script_hex']); ops = []; pos = 0
        while pos < len(raw):
            op = raw[pos]; pos += 1; ops.append(op)
            if op <= 75: pos += op
            elif op in (76, 77, 78):
                size = (1, 2, 4)[op - 76]
                count = int.from_bytes(raw[pos:pos+size], 'little'); pos += size + count
        self.assertEqual(pos, len(raw))
        self.assertEqual(ops.count(0xaf), 1)  # CHECKMULTISIGVERIFY, first round
        self.assertEqual(ops.count(0xae), 1)  # CHECKMULTISIG, terminal round
        self.assertEqual(ops[-1], 0xae)

    def test_subset_binary_layout_and_full_transaction_sighashes(self):
        for ri in (1, 2):
            params = load(f'gpu_digest_r{ri}_params.json')
            raw = (ROOT / f'digest_r{ri}.bin').read_bytes()
            n, t, total, tail, suffix, prefix = struct.unpack('<6I', raw[:24])
            self.assertEqual((n, t), (150, 9))
            self.assertEqual((total, tail, suffix, prefix), tuple(params[k] for k in ('total_preimage_len', 'tail_section_len', 'tx_suffix_len', 'prefix_remainder_len')))
            payload = (bytes.fromhex(params['prefix_remainder'])
                       + b''.join(bytes.fromhex(p) for p in params['dummy_sig_pushes'])
                       + bytes.fromhex(params['tail_section']) + bytes.fromhex(params['tx_suffix']))
            self.assertEqual(raw[56:-96], payload)
            self.assertEqual(len(raw), 56 + prefix + n * 10 + tail + suffix + 96)
            self.assertLess(prefix, 64)
            for vector in (v for v in load('sighash-vectors.json') if v['round'] == ri):
                omitted = set(vector['subsetPoolIndices'])
                script = (bytes.fromhex(params['pre_hors_section']) + bytes.fromhex(params['hors_section'])
                          + b''.join(bytes.fromhex(p) for i, p in enumerate(params['dummy_sig_pushes']) if n - 1 - i not in omitted)
                          + bytes.fromhex(params['tail_section']))
                self.assertEqual(hashlib.sha256(script).hexdigest(), vector['scriptCodeSha256'])
                tx_suffix = bytearray.fromhex(params['tx_suffix'])
                tx_suffix[:4] = struct.pack('<I', vector['sequence'])
                tx_suffix[-8:-4] = struct.pack('<I', vector['locktime'])
                preimage = bytes.fromhex(params['tx_prefix']) + script + tx_suffix
                self.assertEqual(len(preimage), total)
                self.assertEqual(hashlib.sha256(hashlib.sha256(preimage).digest()).hexdigest(), vector['sighash'])

    def test_pinning_binary_offsets(self):
        raw = (ROOT / 'pinning.bin').read_bytes()
        size, = struct.unpack('<I', raw[32:36])
        total, sequence, locktime = struct.unpack('<3I', raw[36+size:48+size])
        self.assertEqual(len(raw), 48 + size + 96)
        self.assertLessEqual(sequence + 4, size)
        self.assertEqual(locktime + 8, size)
        self.assertEqual((total - size) % 64, 0)
        suffix = raw[36:36+size]
        self.assertEqual(struct.unpack('<I', suffix[sequence:sequence+4])[0], 0x80000000)
        self.assertEqual(struct.unpack('<I', suffix[locktime:locktime+4])[0], 500000000)
