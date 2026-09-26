"""Public candidate membership only; this does not verify cryptographic puzzles."""
import math
import re


def subset_rank(indices):
    if (len(indices) != 9 or any(type(i) is not int for i in indices)
            or indices != sorted(set(indices)) or indices[0] < 0 or indices[-1] >= 150):
        raise ValueError('Invalid raw subset combination')
    rank, low = 0, 0
    for position, value in enumerate(indices):
        rank += sum(math.comb(149-skipped, 8-position) for skipped in range(low, value))
        low = value + 1
    return rank


def validate_candidates_in_range(stage, candidates, unit):
    if stage not in ('pinning', 'round1', 'round2'):
        raise ValueError('Unknown stage')
    if (not isinstance(candidates, list) or len(candidates) > 32
            or any(not isinstance(c, str) or len(c) >= 16384 for c in candidates)):
        raise ValueError('Invalid candidate records')
    records = 0
    for candidate in candidates:
        parts = [p for p in re.split(r'(?=^(?:indices|sequence)=)', candidate, flags=re.M) if p.strip()]
        if not parts:
            raise ValueError('Empty candidate file')
        for part in parts:
            pairs = re.findall(r'^([a-z_]+)=([^\n]+)$', part, re.M)
            fields = dict(pairs)
            if len(fields) != len(pairs):
                raise ValueError('Duplicate candidate fields')
            if stage == 'pinning':
                if any(not re.fullmatch(r'[0-9]+', fields.get(k, '')) for k in ('sequence', 'locktime')):
                    raise ValueError('Malformed pin')
                sequence, locktime = int(fields['sequence']), int(fields['locktime'])
                if not (unit['sequence'] <= sequence < unit['sequence'] + unit['sequenceCount']
                        and unit['locktime'] <= locktime < unit['locktime'] + unit['count']//unit['sequenceCount']):
                    raise ValueError('Pin outside assigned range')
            else:
                raw = fields.get('indices', '')
                if not re.fullmatch(r'[0-9]+(?:,[0-9]+){8}', raw):
                    raise ValueError('Malformed subset')
                rank = subset_rank(list(map(int, raw.split(','))))
                if not int(unit['start']) <= rank < int(unit['start']) + unit['count']:
                    raise ValueError('Subset outside assigned range')
            records += 1
    return records
