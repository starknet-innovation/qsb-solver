"""Instrument only the frozen vector candidate for later CPU differential checks."""
import hashlib

CANDIDATE_TREE = '14f574832dcea8f8f454af45a1849430e4229a09cee148ff9bf1021adc6cdc2c'
ANCHOR = '        int vv;'
TRACE = '        printf("TRACE_SUB indices=%d,%d,%d,%d,%d,%d,%d,%d,%d recid=%d hash=%08x%08x%08x%08x%08x%08x%08x%08x\\n",skip[0],skip[1],skip[2],skip[3],skip[4],skip[5],skip[6],skip[7],skip[8],ri,hs[0],hs[1],hs[2],hs[3],hs[4],hs[5],hs[6],hs[7]);\n'


def instrument(source):
    if hashlib.sha256(source.encode()).hexdigest() != CANDIDATE_TREE:
        raise ValueError('trace source is not the frozen vector candidate')
    if source.count(ANCHOR) != 1:
        raise ValueError('ambiguous trace anchor')
    return source.replace(ANCHOR, TRACE+ANCHOR)
