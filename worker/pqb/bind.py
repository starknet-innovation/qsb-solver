"""Write binding.json for the installed PQB candidate files. Run once at image build."""
import hashlib
import json
import os
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent
FILES = ('grind', 'pqb_handler.py', 'pqb_ranges.py')


def main():
    commit = os.environ.get('SOLVER_COMMIT', '')
    if not re.fullmatch('[a-f0-9]{40}', commit):
        raise SystemExit('SOLVER_COMMIT must be the full solver commit')
    files = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in FILES}
    binding = {'format': 'qsb-pqb-candidate-v1', 'status': 'HOLD', 'solverCommit': commit,
               'cudaArchitecture': os.environ.get('CUDA_ARCH', ''), 'files': files}
    (ROOT / 'binding.json').write_text(json.dumps(binding, indent=1, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
