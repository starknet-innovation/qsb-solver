"""A slow, independent enumeration of a ranked PQB range, for tests only.

It shares no code with the grinder or with pqb: plain integers, hashlib, and the definitions in
pqb's docs (OUTSOURCING.md). It reads the grinder's public problem file and lists every gate hit
of a range in the grinder's hit-line format, so a test can compare the two sets exactly: a missed
trial and an invented hit both show.

This is a development check. It is not the application's verifier and is not shipped in an image.
"""
import hashlib
from itertools import combinations
from math import comb

P = 2 ** 256 - 2 ** 32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
PIN_LT_MIN, PIN_LT_END = 500000000, 1700000000
PIN_SEQ_MIN, PIN_SEQ_END = 0x80000000, 0xFFFFFFFE


def load(path):
    prob = {'slot_offs': [], 'C': {}}
    with open(path) as f:
        for line in f:
            parts = line.split()
            if not parts:
                continue
            key = parts[0]
            if key == 'slot':
                assert int(parts[1]) == len(prob['slot_offs'])
                prob['slot_offs'].append(int(parts[2]))
            elif key == 'B':
                prob['B'] = (int(parts[1], 16), int(parts[2], 16))
            elif key == 'C':
                prob['C'][int(parts[1]), int(parts[2])] = (int(parts[3], 16), int(parts[4], 16))
            elif key == 'preimage':
                prob['preimage'] = bytes.fromhex(parts[1])
            elif key in ('track', 'kind'):
                prob[key] = parts[1]
            else:
                prob[key] = int(parts[1])
    return prob


def _add(a, b):
    """Affine addition on secp256k1; None is the point at infinity."""
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0]:
        if (a[1] + b[1]) % P == 0:
            return None
        lam = 3 * a[0] * a[0] * pow(2 * a[1], -1, P) % P
    else:
        lam = (b[1] - a[1]) * pow(b[0] - a[0], -1, P) % P
    x = (lam * lam - a[0] - b[0]) % P
    return x, (lam * (a[0] - x) - a[1]) % P


_DOUBLES = {}


def _mul(k, pt):
    table = _DOUBLES.get(pt)
    if table is None:                       # pt, 2 pt, 4 pt, ...: the base is fixed per problem
        table, q = [], pt
        for _ in range(256):
            table.append(q)
            q = _add(q, q)
        _DOUBLES[pt] = table
    out, i = None, 0
    while k:
        if k & 1:
            out = _add(out, table[i])
        k >>= 1
        i += 1
    return out


def _sha256d(b):
    return hashlib.sha256(hashlib.sha256(b).digest()).digest()


def _encodings(pt, nenc):
    x, y = pt[0].to_bytes(32, 'big'), pt[1].to_bytes(32, 'big')
    out = [bytes([2 + (pt[1] & 1)]) + x, b'\x04' + x + y, bytes([6 + (pt[1] & 1)]) + x + y]
    return out[:nenc]


def _hits_of_z(prob, zbytes):
    """(j, recid, encoding, level) of every gate hit for one sighash."""
    shift = 32 - prob['gate_bits']
    want = prob['gate_tag'] >> shift
    w = _mul(int.from_bytes(zbytes, 'big') % N, prob['B'])
    out = []
    for j in range(prob['K']):
        for rid in range(prob['npts']):
            q = _add(w, prob['C'][j, rid])
            if q is None:
                continue
            for enc, key in enumerate(_encodings(q, prob['nenc'])):
                d = key
                for lvl in range(1, prob['H'] + 1):
                    d = hashlib.sha256(d).digest()
                    if int.from_bytes(d[:4], 'big') >> shift == want:
                        out.append((j, rid, enc, lvl))
    return out


def pin_hits(prob, seq, seq_count, lt_start, lt_count):
    assert prob['kind'] == 'pin'
    assert PIN_SEQ_MIN <= seq and seq + seq_count <= PIN_SEQ_END
    assert PIN_LT_MIN <= lt_start and lt_start + lt_count <= PIN_LT_END
    lines = []
    pre = bytearray(prob['preimage'])
    for s in range(seq, seq + seq_count):
        pre[prob['seq_off']:prob['seq_off'] + 4] = s.to_bytes(4, 'little')
        for lt in range(lt_start, lt_start + lt_count):
            pre[prob['lt_off']:prob['lt_off'] + 4] = lt.to_bytes(4, 'little')
            for h in _hits_of_z(prob, _sha256d(bytes(pre))):
                lines.append('%d %d %d %d %d %d' % ((s, lt) + h))
    return sorted(lines)


def prefix_total(prob):
    return comb(prob['n_slots'] - 1, prob['t'] - 1)


def prefixes(prob, start, count):
    """The (t-1)-prefixes of lexicographic rank [start, start + count)."""
    n, t = prob['n_slots'], prob['t']
    out = []
    for i, pre in enumerate(combinations(range(n - 1), t - 1)):   # lexicographic by construction
        if i >= start + count:
            break
        if i >= start:
            out.append(pre)
    return out


def subset_rank(subset, n):
    """Rank of a sorted subset among the len(subset)-subsets of range(n), lexicographic."""
    rank, prev, t = 0, -1, len(subset)
    for k, x in enumerate(subset):
        for y in range(prev + 1, x):
            rank += comb(n - y - 1, t - k - 1)
        prev = x
    return rank


def round_subsets(prob, start, count):
    n = prob['n_slots']
    return [pre + (last,) for pre in prefixes(prob, start, count) for last in range(pre[-1] + 1, n)]


def round_hits(prob, subsets):
    assert prob['kind'] == 'round'
    lines = []
    pre, offs, slen = prob['preimage'], prob['slot_offs'], prob['slot_len']
    for sub in subsets:
        b, last = bytearray(), 0
        for i in sub:
            b += pre[last:offs[i]]
            last = offs[i] + slen
        b += pre[last:]
        for h in _hits_of_z(prob, _sha256d(bytes(b))):
            lines.append('%s %d %d %d %d' % ((','.join(map(str, sub)),) + h))
    return sorted(lines)


def unrank(rank, n, t):
    """The rank-th t-subset of range(n), lexicographic."""
    out, x = [], 0
    while len(out) < t:
        c = comb(n - x - 1, t - len(out) - 1)
        if rank < c:
            out.append(x)
        else:
            rank -= c
        x += 1
    return tuple(out)


def round_subsets_at(prob, start, count):
    """`round_subsets` for a range anywhere in the space: unrank each prefix on its own."""
    n, t = prob['n_slots'], prob['t']
    assert 0 <= start and start + count <= comb(n - 1, t - 1)
    out = []
    for rank in range(start, start + count):
        pre = unrank(rank, n - 1, t - 1)
        out += [pre + (last,) for last in range(pre[-1] + 1, n)]
    return out


def pin_digest(prob, line):
    """The digest a pin hit line names, re-derived from the problem."""
    seq, lt, j, rid, enc, lvl = (int(x) for x in line.split())
    pre = bytearray(prob['preimage'])
    pre[prob['seq_off']:prob['seq_off'] + 4] = seq.to_bytes(4, 'little')
    pre[prob['lt_off']:prob['lt_off'] + 4] = lt.to_bytes(4, 'little')
    w = _mul(int.from_bytes(_sha256d(bytes(pre)), 'big') % N, prob['B'])
    d = _encodings(_add(w, prob['C'][j, rid]), prob['nenc'])[enc]
    for _ in range(lvl):
        d = hashlib.sha256(d).digest()
    return d


def pin_point(prob, seq, lt):
    """W = z * B for one pinning nonce."""
    pre = bytearray(prob['preimage'])
    pre[prob['seq_off']:prob['seq_off'] + 4] = seq.to_bytes(4, 'little')
    pre[prob['lt_off']:prob['lt_off'] + 4] = lt.to_bytes(4, 'little')
    return _mul(int.from_bytes(_sha256d(bytes(pre)), 'big') % N, prob['B'])
