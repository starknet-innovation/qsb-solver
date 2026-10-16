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
    if (binding.get('format') not in ('qsb-combined-candidate-v1', 'qsb-combined-candidate-v2')
            or binding.get('status') != 'HOLD'
            or not re.fullmatch('[a-f0-9]{40}', binding.get('solverCommit', ''))
            or set(binding.get('files', {})) != REQUIRED):
        raise ValueError('Invalid combined release binding')
    version = binding.get('scriptVersion')
    if ((binding['format'] == 'qsb-combined-candidate-v1' and version is not None)
            or (binding['format'] == 'qsb-combined-candidate-v2'
                and version != historical_handler.CORRECTED_SCRIPT_VERSION)):
        raise ValueError('Invalid combined script binding')
    for name, expected in binding['files'].items():
        file = root / name
        if file.is_symlink() or hashlib.sha256(file.read_bytes()).hexdigest() != expected:
            raise ValueError('Installed combined artifact mismatch: ' + name)
    return binding


def handler(event):
    binding = release_binding()
    # Legacy wire name: this is the combined repository commit, not either upstream lineage.
    historical_handler.PINNED_KERNEL = binding['solverCommit']
    if binding['format'] == 'qsb-combined-candidate-v2':
        return historical_handler.handler(event, script_version=binding['scriptVersion'])
    return historical_handler.handler(event)
