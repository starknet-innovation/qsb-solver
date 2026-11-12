"""Write the correctness cases of the native measurement run and their expected hit sets.

    python3 research/pqb-ranked/measure/make_expected.py

Expected hits come from the independent reference (tests/reference.py), never from the grinder.
Also writes fixtures/pin-planted.txt: the pin problem with menu point C[0][0] set to one z-block's
sighash point and C[0][1] to its negative, the exceptional case the device formulas cannot add.
"""
import hashlib
import json
import sys
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'tests'))
import reference  # noqa: E402

FIXTURES = HERE.parent / 'tests' / 'fixtures'
SMALL = {'QG_NZ_MAX': '256'}
PLANT = (0x8000000A, 900000021)


def problem_bytes(name, gate_bits):
    raw = (FIXTURES / (name + '.txt')).read_bytes()
    assert raw.count(b'gate_bits 12\n') == 1
    return raw.replace(b'gate_bits 12\n', b'gate_bits %d\n' % gate_bits)


def planted():
    prob = reference.load(FIXTURES / 'pin.txt')
    w = reference.pin_point(prob, *PLANT)
    lines = problem_bytes('pin', 3).decode().split('\n')
    for i, ln in enumerate(lines):
        if ln.startswith('C 0 0 '):
            lines[i] = 'C 0 0 %064x %064x' % w
        elif ln.startswith('C 0 1 '):
            lines[i] = 'C 0 1 %064x %064x' % (w[0], reference.P - w[1])
    (FIXTURES / 'pin-planted.txt').write_text('\n'.join(lines))
    return reference.load(FIXTURES / 'pin-planted.txt')


def der_shape(d):
    lr = d[3]
    return 1 <= lr <= 24 and d[4 + lr] == 2 and d[5 + lr] == 25 - lr


def main():
    cases = []

    def pin(label, prob, problem, gate_bits, seq, seq_count, lt, lt_count, env=None, exact=0, der=False):
        prob = dict(prob, gate_bits=gate_bits)
        gate = reference.pin_hits(prob, seq, seq_count, lt, lt_count)
        hits = [h for h in gate if der_shape(reference.pin_digest(prob, h))] if der else gate
        cases.append({'label': label, 'problem': problem, 'gateBits': gate_bits, 'env': env or {},
                      'args': ['--pin-seq', seq, '--pin-seq-count', seq_count, '--pin-lt-start', lt,
                               '--pin-lt-count', lt_count] + (['--der-filter', 1] if der else []),
                      'zblocks': seq_count * lt_count, 'gateHits': len(gate), 'exactZblocks': exact, 'hits': hits})

    def rnd(label, name, start, count, env=None):
        prob = reference.load(FIXTURES / (name + '.txt'))
        subsets = reference.round_subsets_at(prob, start, count)
        hits = reference.round_hits(prob, subsets)
        cases.append({'label': label, 'problem': name + '.txt', 'gateBits': 12, 'env': env or {},
                      'args': ['--prefix-start', start, '--prefix-count', count], 'zblocks': len(subsets),
                      'gateHits': len(hits), 'exactZblocks': 0, 'hits': hits})

    p = reference.load(FIXTURES / 'pin.txt')
    pin('pin-first', p, 'pin.txt', 12, 0x80000000, 2, 500000000, 1500)
    pin('pin-last', p, 'pin.txt', 12, 0xFFFFFFFD, 1, 1699998500, 1500)
    pin('pin-batches', p, 'pin.txt', 12, 0x80000003, 3, 1234567890, 900, SMALL)
    pin('pin-der-filter', p, 'pin.txt', 1, 0x80000005, 1, 600000000, 64, der=True)
    # A filtered case that must EMIT candidates. Shaped hits are about 2^-20 per trial, so the two
    # windows were located beforehand with the emulated grinder; the expected sets below are still
    # computed here by the reference alone, and must each hold a shaped hit.
    pin('pin-der-filter-emits', p, 'pin.txt', 1, 0x80000006, 1, 700019040, 16, der=True)
    pin('pin-der-filter-emits-uncompressed', p, 'pin.txt', 1, 0x80000006, 1, 700040024, 16, der=True)
    assert all(c['hits'] for c in cases[-2:]), 'a filtered case expects no candidate'
    pin('pin-planted-exceptional', planted(), 'pin-planted.txt', 3, PLANT[0], 1, 900000000, 48, exact=4)
    for name, n, t in (('round0', 109, 8), ('round1', 101, 9)):
        total = comb(n - 1, t - 1)
        rnd(name + '-first', name, 0, 10)
        rnd(name + '-last', name, total - 300, 300)
        rnd(name + '-interior-batches', name, total // 3, 40 if name == 'round0' else 150, SMALL)
    files = {f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(FIXTURES.glob('*.txt'))}
    out = {'format': 'qsb-pqb-measure-expected-v1', 'fixtures': files, 'cases': cases}
    (HERE / 'expected.json').write_text(json.dumps(out, indent=1) + '\n')
    for c in cases:
        print('%-26s %6d z-blocks %5d hits' % (c['label'], c['zblocks'], len(c['hits'])))


if __name__ == '__main__':
    main()
