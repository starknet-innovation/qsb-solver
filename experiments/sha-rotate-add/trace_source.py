"""Instrument only the frozen tree.cu for later CPU differential checks.

The rotate-add patch does not touch tree.cu, so the frozen tree is the committed one.
The trace receipt binds the patched GPUHash.h separately.
"""
import hashlib

CANDIDATE_TREE = '71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb'
CANDIDATE_GPUHASH = 'ac7c11110b5ccf205eb2ee007e0163439540e58dba80d21904f86ec29ec1c807'
ANCHOR = '        int vv;'
TRACE = '        printf("TRACE_SUB indices=%d,%d,%d,%d,%d,%d,%d,%d,%d recid=%d hash=%08x%08x%08x%08x%08x%08x%08x%08x\\n",skip[0],skip[1],skip[2],skip[3],skip[4],skip[5],skip[6],skip[7],skip[8],ri,hs[0],hs[1],hs[2],hs[3],hs[4],hs[5],hs[6],hs[7]);\n'


def instrument(source):
    if hashlib.sha256(source.encode()).hexdigest() != CANDIDATE_TREE:
        raise ValueError('trace source is not the frozen tree')
    if source.count(ANCHOR) != 1:
        raise ValueError('ambiguous trace anchor')
    return source.replace(ANCHOR, TRACE+ANCHOR)
