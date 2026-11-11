"""Durable, one-shot API handoff to the connected AWS MCP tool, without a local AWS CLI.

The operator services each *.request.json once with call_boto3, persisting *.dispatched before
the call and *.response.json afterwards. A lost response is uncertain: reconcile, never replay.
All files stay outside Git. This transport never calls AWS or reads credentials itself.
"""
import json
from pathlib import Path
import time
import uuid


def exchange(directory, region, service, operation, params, timeout=180):
    root = Path(directory).resolve()
    if any((parent / '.git').exists() for parent in (root, *root.parents)):
        raise ValueError('MCP handoff receipts must be outside Git')
    root.mkdir(parents=True, exist_ok=True)
    identity = '%020d-%s' % (time.time_ns(), uuid.uuid4().hex)
    request = {'id': identity, 'region': region, 'service': service,
               'operation': ''.join(part.title() for part in operation.split('-')), 'params': params}
    pending = root / (identity + '.partial')
    pending.write_text(json.dumps(request, indent=1) + '\n')
    pending.rename(root / (identity + '.request.json'))
    response = root / (identity + '.response.json')
    deadline = time.monotonic() + timeout
    while not response.exists():
        if time.monotonic() >= deadline:
            raise TimeoutError('Uncertain MCP handoff; reconcile request ' + identity)
        time.sleep(0.1)
    value = json.loads(response.read_text())
    if 'error' in value:
        raise RuntimeError(value['error'])
    return value['result']
