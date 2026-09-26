"""Run public hash-bound image regression; no wallet or provider credentials."""
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
import http.server
import functools


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
            allowed={'capacity','capacity.diff','forced-exception','forced-exception.diff','detected-exception','detected-exception.diff','receipt.json','source-commit.txt','fixtures.json'}
            if len(members)!=len(allowed) or {m.name for m in members}!=allowed or any(not m.isfile() or m.size>10_000_000 for m in members):
                raise ValueError('unexpected archive inventory')
            for member in members:
                (root/member.name).write_bytes(archive.extractfile(member).read())
        runner=root/'runner.py'
        runner.write_bytes(download(os.environ['RUNNER_URL'],os.environ['RUNNER_SHA256']))
        serve=root/'public';serve.mkdir()
        result=serve/'result.json'
        proc=subprocess.run(['python3','-u',str(runner),str(root),str(result)],timeout=1200)
        print('QSB_REGRESSION_EXIT',proc.returncode,flush=True)
        if proc.returncode==0:
            server=http.server.HTTPServer(('0.0.0.0',8000),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(serve)))
            server.timeout=5
            deadline=time.monotonic()+300
            while time.monotonic()<deadline:server.handle_request()



if __name__=='__main__':
    main()
