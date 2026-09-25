"""Run public hash-bound pinning diagnostics; no wallet or provider credentials."""
import base64
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time
import urllib.request
import zlib


def download(url, expected):
    if not url.startswith(('https://github.com/starknet-innovation/qsb-solver/',
                           'https://raw.githubusercontent.com/starknet-innovation/qsb-solver/')):
        raise ValueError('unexpected artifact origin')
    with urllib.request.urlopen(url, timeout=30) as response:
        data=response.read(10_000_001)
    if len(data)>10_000_000 or hashlib.sha256(data).hexdigest()!=expected:
        raise ValueError('artifact integrity mismatch')
    return data


def main():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        data=download(os.environ['AUDIT_URL'],os.environ['AUDIT_SHA256'])
        with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as archive:
            members=archive.getmembers()
            allowed={'pinning','pinning-audit','receipt.json','source-commit.txt','params.bin'}
            if len(members)!=len(allowed) or {m.name for m in members}!=allowed or any(not m.isfile() or m.size>10_000_000 for m in members):
                raise ValueError('unexpected archive inventory')
            for member in members:
                (root/member.name).write_bytes(archive.extractfile(member).read())
        runner=root/'runner.py'
        runner.write_bytes(download(os.environ['RUNNER_URL'],os.environ['RUNNER_SHA256']))
        proc=subprocess.run(['python3','-u',str(runner),'--artifacts',str(root),
                             '--params',str(root/'params.bin'),'--output',str(root/'result.json')],timeout=1250)
        if proc.returncode==0:
            result=(root/'result.json').read_bytes()
            print('QSB_PINNING_RESULT',base64.b64encode(zlib.compress(result)).decode(),flush=True)
            print('QSB_PINNING_RESULT_SHA256',hashlib.sha256(result).hexdigest(),flush=True)
        print('QSB_PINNING_EXIT',proc.returncode,flush=True)
        time.sleep(120)


if __name__=='__main__':
    main()
