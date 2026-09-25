"""Public-artifact-only pod bootstrap; no provider credentials or wallet inputs."""
import hashlib
import io
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time
import urllib.request


def download(url, expected):
    if not url.startswith(('https://github.com/starknet-innovation/qsb-solver/',
                           'https://raw.githubusercontent.com/starknet-innovation/qsb-solver/')):
        raise ValueError('unexpected artifact origin')
    with urllib.request.urlopen(url, timeout=30) as response:
        data = response.read(10_000_001)
    if len(data) > 10_000_000 or hashlib.sha256(data).hexdigest() != expected:
        raise ValueError('artifact integrity mismatch')
    return data


def main():
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        data = download(os.environ['AUDIT_URL'], os.environ['AUDIT_SHA256'])
        with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as archive:
            allowed = {'point-audit', 'vectors.bin', 'receipt.json', 'source-commit.txt'}
            members = archive.getmembers()
            if len(members) != len(allowed) or {m.name for m in members} != allowed or any(not m.isfile() for m in members):
                raise ValueError('unexpected archive members')
            for member in members:
                (root/member.name).write_bytes(archive.extractfile(member).read())
        runner = root/'run_curve.py'
        runner.write_bytes(download(os.environ['RUNNER_URL'], os.environ['RUNNER_SHA256']))
        result = subprocess.run(['python3', '-u', str(runner), str(root), os.environ['RECEIPT_SHA256']], timeout=200)
        print('QSB_CURVE_EXIT', result.returncode, flush=True)
        # Keep terminal logs retrievable until operator deletion; external watchdog mandatory.
        time.sleep(600)


if __name__ == '__main__':
    main()
