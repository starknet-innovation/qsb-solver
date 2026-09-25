"""Bind the actual combined image outputs. Does not grant promotion approval."""
import hashlib
import json
import os
import pathlib
import re

def bind(ROOT, commit, architecture):
    if not re.fullmatch('[a-f0-9]{40}', commit):
        raise ValueError('An exact source commit is required')
    receipt = json.loads((ROOT / 'optimized-build-receipt.json').read_text())
    expected='sm_'+architecture
    if architecture not in ('86','89') or (ROOT/'source/pinning/cuda-architecture').read_text().strip()!=architecture:
        raise ValueError('Pinning architecture mismatch')
    if receipt.get('architecture')!=expected or receipt.get('flags', []).count('-arch='+expected)!=1:
        raise ValueError('Subset architecture mismatch')
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    if sha(ROOT / 'subset') != receipt['binarySha256']:
        raise ValueError('Optimized binary differs from its build receipt')
    binding = {
        'format': 'qsb-combined-candidate-v1', 'status': 'HOLD',
        'solverCommit': commit, 'searchVersion': 'ranked-v2', 'architecture': expected,
        'pinningUpstreamCommit': '2791ed0588f5014ccd688d48ba5502df2879f2f1',
        'subsetUpstreamCommit': '1650caf53a32b0ea16aae9e490ebbf5a8686d632',
        'subsetSourceLockSha256': receipt['sourceLockSha256'],
        'files': {name: sha(ROOT / name) for name in (
            'pinning', 'subset', 'handler.py', 'historical_handler.py', 'search_ranges.py')},
    }
    (ROOT / 'pipeline.json').write_text(json.dumps(binding, sort_keys=True, indent=2) + '\n')

if __name__=='__main__':
    bind(pathlib.Path('/opt/qsb'),os.environ['SOLVER_COMMIT'],os.environ['CUDA_ARCH'])
