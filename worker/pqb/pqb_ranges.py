"""pqb-ranked-v2: deterministic, disjoint work units for the three PQB stages.

Every unit is a contiguous range of pqb's own nonces (`start`, `count`), so a result can be
checked with pqb's definitions. Interrupted units are replayed in full.

  pinning   nonce = (nSequence - 0x80000000) * 1,200,000,000 + (nLockTime - 500,000,000).
            A unit is SEQUENCES consecutive nSequence values, each with every usable nLockTime.
  round0/1  nonce = lexicographic rank of a t-subset of the live table slots. A unit is
            PREFIX_CHUNK[stage] consecutive (t-1)-prefixes, each with all its completions; subsets
            that share a prefix are contiguous in lexicographic order.

The shapes are the ones of pqb's `PQB` configuration. A different table size, pick count or unit
size is a different partition and needs a new searchVersion.

Unit sizes are set so the largest unit of each stage takes about eight minutes at the rates
measured on one A10G on 2026-11-11 (docs/pqb/2026-11-11-a10g-measurement.md): 486 s, 502 s and
486 s. That leaves room under a 900-second job limit for start-up and a slower host; it is a
sizing choice from one host's rates, not a guarantee. pqb-ranked-v1 (16 sequences, 2^30
prefixes for both rounds) was provisional and never published or enrolled.
"""
from math import comb

VERSION = 'pqb-ranked-v2'
LT_MIN, LT_END = 500000000, 1700000000
LT_SPAN = LT_END - LT_MIN
SEQ_MIN, SEQ_COUNT = 0x80000000, 0x7FFFFFFE          # 0x80000000 .. 0xFFFFFFFD
SEQUENCES = 14                                       # divides the 2^31 - 2 usable values exactly
PREFIX_CHUNK = {'round0': 3 << 27, 'round1': 1 << 30}
ROUNDS = {'round0': (109, 8), 'round1': (101, 9)}    # live table slots, picks


def _subset_rank(subset, n):
    rank, prev, t = 0, -1, len(subset)
    for k, x in enumerate(subset):
        for y in range(prev + 1, x):
            rank += comb(n - y - 1, t - k - 1)
        prev = x
    return rank


def _unrank(rank, n, t):
    out, x = [], 0
    while len(out) < t:
        c = comb(n - x - 1, t - len(out) - 1)
        if rank < c:
            out.append(x)
        else:
            rank -= c
        x += 1
    return out


def prefix_total(stage):
    n, t = ROUNDS[stage]
    return comb(n - 1, t - 1)


def subset_rank_of_prefix(stage, prefix_rank):
    """The first subset rank whose (t-1)-prefix has this rank; the total for the end."""
    n, t = ROUNDS[stage]
    if prefix_rank == comb(n - 1, t - 1):
        return comb(n, t)
    prefix = _unrank(prefix_rank, n - 1, t - 1)
    return _subset_rank(prefix + [prefix[-1] + 1], n)


def work_range(stage, attempt):
    if type(attempt) is not int or attempt < 0:
        raise ValueError('Invalid work unit')
    if stage == 'pinning':
        offset = attempt * SEQUENCES
        if offset >= SEQ_COUNT:
            raise ValueError('Search range exhausted')
        count = min(SEQUENCES, SEQ_COUNT - offset)
        return {'version': VERSION, 'start': str(offset * LT_SPAN), 'count': count * LT_SPAN,
                'sequence': SEQ_MIN + offset, 'sequenceCount': count,
                'locktime': LT_MIN, 'locktimeCount': LT_SPAN}
    if stage not in ROUNDS:
        raise ValueError('Invalid stage')
    total = prefix_total(stage)
    chunk = PREFIX_CHUNK[stage]
    first = attempt * chunk
    if first >= total:
        raise ValueError('Search range exhausted')
    count = min(chunk, total - first)
    start = subset_rank_of_prefix(stage, first)
    return {'version': VERSION, 'start': str(start),
            'count': subset_rank_of_prefix(stage, first + count) - start,
            'prefixStart': str(first), 'prefixCount': count}


def unit_count(stage):
    if stage == 'pinning':
        return -(-SEQ_COUNT // SEQUENCES)
    return -(-prefix_total(stage) // PREFIX_CHUNK[stage])
