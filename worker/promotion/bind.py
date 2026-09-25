"""Bind the actual combined image outputs. Does not grant promotion approval."""
import hashlib
import json
import os
import pathlib
import re

ROOT = pathlib.Path('/opt/qsb')
commit = os.environ['SOLVER_COMMIT']
if not re.fullmatch('[a-f0-9]{40}', commit):
    raise ValueError('An exact source commit is required')
receipt = json.loads((ROOT / 'optimized-build-receipt.json').read_text())
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
if sha(ROOT / 'subset') != receipt['binarySha256']:
    raise ValueError('Optimized binary differs from its build receipt')
binding = {
    'format': 'qsb-combined-candidate-v1', 'status': 'HOLD',
    'solverCommit': commit, 'searchVersion': 'ranked-v2',
    'pinningUpstreamCommit': '2791ed0588f5014ccd688d48ba5502df2879f2f1',
    'subsetUpstreamCommit': '1650caf53a32b0ea16aae9e490ebbf5a8686d632',
    'subsetSourceLockSha256': receipt['sourceLockSha256'],
    'files': {name: sha(ROOT / name) for name in (
        'pinning', 'subset', 'handler.py', 'historical_handler.py', 'search_ranges.py')},
}
(ROOT / 'pipeline.json').write_text(json.dumps(binding, sort_keys=True, indent=2) + '\n')
