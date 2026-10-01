"""Download only pinned public verifier files and stage the frozen saved event."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import urllib.request


def prepare(output):
    base = Path(__file__).resolve().parent
    lock = json.loads((base / 'first-verdict-fixture-lock.json').read_text())
    output.mkdir(exist_ok=False)
    reference = output / 'reference'
    reference.mkdir()
    for name, wanted in lock['files'].items():
        if name == 'event.json':
            data = gzip.decompress((base / 'evidence/first-verdict-event.json.gz').read_bytes())
            target = output / name
        else:
            if name not in {'handler.py', 'qsb_pipeline.py', 'verify_hit.py',
                            'gpu_emulator.py', 'secp256k1.py', 'bitcoin_tx.py', 'LICENSE'}:
                raise ValueError('unexpected reference file')
            url = ('https://raw.githubusercontent.com/starknet-innovation/qsb-app/'
                   + lock['appCommit'] + '/worker/cpu/' + name)
            with urllib.request.urlopen(url, timeout=30) as response:
                data = response.read(2 * 1024 * 1024 + 1)
            if len(data) > 2 * 1024 * 1024:
                raise ValueError('oversized reference')
            target = reference / name
        if hashlib.sha256(data).hexdigest() != wanted:
            raise ValueError('fixture hash mismatch: ' + name)
        target.write_bytes(data)


if __name__ == '__main__':
    prepare(Path(sys.argv[1]))
