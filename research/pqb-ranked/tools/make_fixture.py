"""Write the public test problems under tests/fixtures from a pqb checkout.

    PQB_ROOT=/path/to/pqb python3 research/pqb-ranked/tools/make_fixture.py

The lock is built from a seed that is published here on purpose: it is a synthetic test vault,
it must never be funded, and nothing derived from it is a secret. The outputs are pqb's own
public work packets (script, transaction template, menu points) and the grinder problems made
from them. Needs pqb's dependencies (coincurve).
"""
import hashlib
import json
import os
import sys

ROOT = os.environ.get('PQB_ROOT')
if not ROOT:
    sys.exit('set PQB_ROOT to a fireblocks-labs/pqb checkout')
sys.path.insert(0, os.path.join(ROOT, 'pqb', 'src'))
from pqb import gpu, grind  # noqa: E402
from pqb.lock import Lock  # noqa: E402

SEED = hashlib.sha256(b'qsb-solver pqb-ranked public test fixture v1').digest()
PIN_NONCE = 987654321012
ROUND0_SELECTION = [3, 14, 15, 26, 53, 58, 79, 97]
GATE_BITS = 12          # many hits per z-block, so a small range is a real completeness test
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tests', 'fixtures')


def tx_hex():
    from test_framework.messages import CTransaction, CTxIn, CTxOut, COutPoint, CTxInWitness
    tx = CTransaction()
    tx.version = 2
    tx.vin.append(CTxIn(COutPoint(int('11' * 32, 16), 0), b'', 0xFFFFFFFF))
    tx.vout.append(CTxOut(90000, bytes.fromhex('0014' + '11' * 20)))
    tx.wit.vtxinwit = [CTxInWitness()]
    return tx.serialize().hex()


def main():
    lock = Lock.new('PQB', seed=SEED)
    packets = grind.packets_for_lock(lock, tx_hex(), pin_nonce=PIN_NONCE,
                                     prior_selections=[ROUND0_SELECTION])
    os.makedirs(OUT, exist_ok=True)
    names = []
    for p in packets:
        prob = gpu.problem_from_packet(p, gate_bits=GATE_BITS)
        gpu.check_problem(p, prob, samples=8)
        name = prob['track']
        with open(os.path.join(OUT, name + '.txt'), 'w') as f:
            f.write(gpu.problem_txt(prob))
        with open(os.path.join(OUT, name + '.packet.json'), 'w') as f:
            json.dump(p.raw, f, sort_keys=True, separators=(',', ':'))
            f.write('\n')
        names.append(name)
    print('wrote', ', '.join(names), 'to', os.path.normpath(OUT))


if __name__ == '__main__':
    main()
