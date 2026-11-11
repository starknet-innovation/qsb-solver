"""pqb's own cost model, with the rounds swept exhaustively instead of drawn at random.

    PQB_ROOT=/path/to/pqb python3 research/pqb-ranked/tools/cost_model.py

A MODEL, not a measurement. It takes pqb's stage geometry, solve probability and published
RTX 4090 trial rates (`pqb.fleet`), and assumes a ranked sweep runs at the same trials per second
as pqb's random draws, which nothing here has measured. A round holds K ~ Poisson(lam) solutions
at uniform positions: a fixed-order sweep meets the first after space / (K + 1) on average and
proves an empty round after exactly one pass, where random draws must be abandoned at a cut-off.
"""
import hashlib
import math
import os
import sys

ROOT = os.environ.get('PQB_ROOT')
if not ROOT:
    sys.exit('set PQB_ROOT to a fireblocks-labs/pqb checkout')
sys.path.insert(0, os.path.join(ROOT, 'pqb', 'src'))
from pqb import fleet  # noqa: E402
from pqb.lock import Lock  # noqa: E402

FLEET_MEAN = {'pin': 5.61e9, 'round0': 6.14e9, 'round1': 4.30e9}   # pqb docs/OUTSOURCING.md


def sweep_terms(lam, kmax=80):
    """(expected time in units of 1/p trials, P(empty)) for one exhaustive pass."""
    e = pk = math.exp(-lam)
    e *= lam
    for k in range(1, kmax):
        pk *= lam / k
        e += pk * lam / (k + 1)
    return e, math.exp(-lam)


def main():
    lock = Lock.new('PQB', seed=hashlib.sha256(b'qsb-solver pqb-ranked public test fixture v1').digest())
    for label, rates in (('pqb card sweep, one RTX 4090', None), ('pqb 16-card fleet mean', FLEET_MEAN)):
        models = fleet.stage_models(lock, rates)
        random_total = fleet._total_hours(models, [m.cutoff for m in models[1:]])
        num, alive = models[0].unit_h, 1.0
        print(label)
        print('  pin      %.2f h expected' % models[0].unit_h)
        for m in models[1:]:
            e, f = sweep_terms(m.lam)
            print('  %s   full pass %.2f h, P(empty) %.3f, expected %.2f h (random draws give up at %.2fx)'
                  % (m.track, m.lam * m.unit_h, f, e * m.unit_h, m.cutoff))
            num += alive * e * m.unit_h
            alive *= 1 - f
        print('  whole spend, re-pins included: random draws %.2f h, exhaustive sweep %.2f h (x%.3f)'
              % (random_total, num / alive, num / alive / random_total))


if __name__ == '__main__':
    main()
