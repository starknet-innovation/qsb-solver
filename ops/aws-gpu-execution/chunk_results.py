"""Collect bounded public SSM output chunks; never resubmit an uncertain read."""
import base64
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import time
from ssm_command import bash_command


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream); stream.flush(); os.fsync(stream.fileno())
    fd = os.open(path.parent, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)


def metadata(stdout):
    rows = [s[len('QSB_PUBLIC_RESULT_META='):] for s in stdout.splitlines()
            if s.startswith('QSB_PUBLIC_RESULT_META=')]
    if len(rows) != 1: raise ValueError('missing or duplicate public result metadata')
    meta = json.loads(rows[0])
    if type(meta.get('bytes')) is not int or not 0 < meta['bytes'] <= 2000000:
        raise ValueError('invalid public result size')
    digest = meta.get('sha256', '')
    if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
        raise ValueError('invalid result digest')
    return meta


def decode(data, meta):
    if len(data) != meta['bytes'] or hashlib.sha256(data).hexdigest() != meta['sha256']:
        raise ValueError('result integrity mismatch')
    compressed = base64.b64decode(data, validate=True)
    with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
        raw = stream.read(8000001)
    if len(raw) > 8000000: raise ValueError('decoded result too large')
    value = json.loads(raw)
    if not isinstance(value, dict) or not all(isinstance(k, str) and isinstance(v, str)
        and Path(k).name == k and k not in ('', '.', '..') for k, v in value.items()):
        raise ValueError('result must contain flat text files')
    return value


def collect(directory, instance, stdout, aws, deadline, sleep=time.sleep):
    meta = metadata(stdout)
    directory.mkdir(exist_ok=True)
    chunks = []
    for start in range(0, meta['bytes'], 18000):
        if time.time() + 120 >= deadline: raise TimeoutError('collection deadline')
        count = min(18000, meta['bytes'] - start)
        intent = directory / f'{start}-intent.json'
        response = directory / f'{start}-command.json'
        result = directory / f'{start}-result.json'
        code = "import pathlib,sys;d=pathlib.Path('/var/tmp/qsb-a10g-results/public-result.b64').read_bytes();sys.stdout.write(d[%d:%d].decode('ascii'))" % (start, start + count)
        request = {'InstanceIds':[instance], 'DocumentName':'AWS-RunShellScript',
                   'Parameters':{'commands':[bash_command("python3 - <<'PY'\n" + code + '\nPY')],
                                 'executionTimeout':['30']}, 'TimeoutSeconds':60}
        if intent.exists():
            if json.loads(intent.read_text()) != request: raise ValueError('chunk intent mismatch')
            if not response.exists(): raise ValueError('uncertain chunk send; reconcile before resuming')
        else:
            save(intent, request)
            save(response, aws('ssm', 'send-command', '--cli-input-json', json.dumps(request)))
        cid = json.loads(response.read_text())['Command']['CommandId']
        if result.exists():
            row = json.loads(result.read_text())
        else:
            end = min(time.time() + 90, deadline - 120)
            while True:
                if time.time() >= end: raise TimeoutError('chunk read timed out')
                sleep(2)
                row = aws('ssm', 'get-command-invocation', '--command-id', cid, '--instance-id', instance)
                if row['CommandId'] != cid or row['InstanceId'] != instance: raise ValueError('chunk identity mismatch')
                if row['Status'] in ('Pending', 'InProgress', 'Delayed'): continue
                save(result, row); break
        if row['CommandId'] != cid or row['InstanceId'] != instance or row['Status'] != 'Success' or row.get('ResponseCode') != 0:
            raise ValueError('chunk failed or mismatched')
        data = row['StandardOutputContent'].encode('ascii')
        if len(data) != count: raise ValueError('truncated chunk')
        chunks.append(data)
    return decode(b''.join(chunks), meta)
