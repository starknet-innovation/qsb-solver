"""Combined candidate worker. Its public results still require independent CPU checks."""
import hashlib
import json
import pathlib
import re
import historical_handler

ROOT = pathlib.Path(__file__).resolve().parent
REQUIRED = {'pinning', 'subset', 'handler.py', 'historical_handler.py', 'search_ranges.py'}


def release_binding(root=ROOT):
    raw = (root / 'pipeline.json').read_bytes()
    binding = json.loads(raw)
    if (binding.get('format') != 'qsb-combined-candidate-v1'
            or binding.get('status') != 'HOLD'
            or not re.fullmatch('[a-f0-9]{40}', binding.get('solverCommit', ''))
            or set(binding.get('files', {})) != REQUIRED):
        raise ValueError('Invalid combined release binding')
    for name, expected in binding['files'].items():
        file = root / name
        if file.is_symlink() or hashlib.sha256(file.read_bytes()).hexdigest() != expected:
            raise ValueError('Installed combined artifact mismatch: ' + name)
    return binding


def handler(event):
    binding = release_binding()
    # Legacy wire name: this is the combined repository commit, not either upstream lineage.
    historical_handler.PINNED_KERNEL = binding['solverCommit']
    return historical_handler.handler(event)


if __name__ == '__main__':
    import runpod
    runpod.serverless.start({'handler': handler})
