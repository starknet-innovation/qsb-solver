"""Explicit Bash transport for AWS-RunShellScript and bounded result decoding."""
import base64
import gzip
import hashlib
import io
import json


def bash_command(script):
    # The outer shell is POSIX sh. Its only job is to exec Bash with literal stdin.
    delimiter = 'QSB_BASH_' + hashlib.sha256(script.encode()).hexdigest()
    while delimiter in script.splitlines():
        delimiter += '_'
    return "exec /bin/bash -s <<'" + delimiter + "'\n" + script + '\n' + delimiter + '\n'


def decode_result(stdout):
    fields = {}
    for prefix in ('RESULT_BASE64=', 'RESULT_SHA256='):
        values = [line[len(prefix):] for line in stdout.splitlines() if line.startswith(prefix)]
        if len(values) != 1:
            raise ValueError('missing or duplicate result envelope: ' + prefix[:-1])
        fields[prefix] = values[0]
    encoded = fields['RESULT_BASE64='].encode('ascii')
    if len(encoded) >= 16000:
        raise ValueError('result envelope exceeds limit')
    if hashlib.sha256(encoded).hexdigest() != fields['RESULT_SHA256=']:
        raise ValueError('result envelope checksum mismatch')
    try:
        compressed = base64.b64decode(encoded, validate=True)
        with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
            raw = stream.read(1024 * 1024 + 1)
        if len(raw) > 1024 * 1024:
            raise ValueError('decoded result exceeds limit')
        value = json.loads(raw)
    except (OSError, EOFError, UnicodeError, json.JSONDecodeError) as error:
        raise ValueError('malformed result envelope') from error
    if not isinstance(value, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in value.items()):
        raise ValueError('result must contain text files')
    return value
