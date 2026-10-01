"""Isolated scalar indexing experiment; never mutate the production source."""
from pathlib import Path
import argparse
import hashlib
import json
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'research/optimized-subset/subset/tests/gpu_epochs/tree.cu'
EXPECTED = '71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb'
SIGNATURE = '__device__ __forceinline__ void qsb_compress_constant_rolled(uint32_t *output)'

def function(source):
    start = source.index(SIGNATURE)
    end = source.index('\n}\n', start) + 2
    return source[start:end]

def transform(source):
    if hashlib.sha256(source.encode()).hexdigest() != EXPECTED:
        raise ValueError('baseline source hash mismatch')
    old = function(source)
    new = old.replace('for(int block=0;block<4;block++){',
        'for(int offset=0;offset<256;){\n        const int stop=offset+64;')
    new = new.replace('for(int r=0;r<64;r+=8){',
        'for(;offset<stop;offset+=8){')
    for n in range(8):
        original = 'QSB_CONST_SCHEDULE[block][r' + (f'+{n}' if n else '') + ']'
        replacement = 'schedule[offset' + (f'+{n}' if n else '') + ']'
        if new.count(original) != 1:
            raise ValueError('compression body drift')
        new = new.replace(original, replacement)
    # A dedicated flat symbol avoids crossing C++ array-subobject bounds.
    new = new.replace(SIGNATURE+'{', SIGNATURE+'{\n    const uint32_t *schedule=QSB_CONST_SCHEDULE;')
    changed = source.replace(old, new, 1)
    changed = changed.replace('__constant__ uint32_t QSB_CONST_SCHEDULE[4][64];',
                              '__constant__ uint32_t QSB_CONST_SCHEDULE[256];', 1)
    # Existing fully-unrolled constant compressor uses the same symbol.
    import re
    changed = re.sub(r'QSB_CONST_SCHEDULE\[block\]\[(\d+)\]',
                     r'QSB_CONST_SCHEDULE[block*64+\1]', changed)
    return changed

def main():
    parser=argparse.ArgumentParser();parser.add_argument('output',type=Path);args=parser.parse_args()
    original=SOURCE.read_text();candidate=transform(original)
    args.output.mkdir(exist_ok=False)
    for name,text in [('baseline',original),('candidate',candidate)]:
        (args.output/(name+'.cu')).write_text(text)
    (args.output/'prepare.json').write_text(json.dumps({
        'baselineSourceSha256':EXPECTED,
        'candidateSourceSha256':hashlib.sha256(candidate.encode()).hexdigest(),
        'gpuExecuted':False,'status':'UNEXECUTED'},indent=2)+'\n')
if __name__=='__main__':main()
