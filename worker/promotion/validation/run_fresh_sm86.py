"""Public-only sm86 proof session. Outputs are evidence, never durable range credit.

One installed handler call reserves its full 840-second timeout plus grace.
The host must enforce a 960-second outer timeout and independent shutdown.
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import time
import uuid

COMMIT = '43c77084648aa0f4cbcb1589abfcc792c9cc0d9d'
PIN = 'cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'
SUB = '673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15'
ALLOWED = {'protocol','stage','parameterBase64','parameterSha256','manifestHash',
           'attempt','sequence','locktime','kernelCommit','searchVersion'}
SESSION_SECONDS = 900
CALL_RESERVE_SECONDS = 860


def validate_batch(batch):
    if not isinstance(batch, dict) or set(batch) != {'batchId','request','maxAttempts'}:
        raise ValueError('Unexpected public batch fields')
    if str(uuid.UUID(batch['batchId'])) != batch['batchId']:
        raise ValueError('Invalid batch ID')
    request = batch['request']
    if not isinstance(request, dict) or set(request) - ALLOWED:
        raise ValueError('Unexpected request fields')
    if request.get('kernelCommit') != COMMIT:
        raise ValueError('Wrong frozen candidate')
    if type(request.get('attempt')) is not int or request['attempt'] < 0:
        raise ValueError('Invalid first attempt')
    if type(batch['maxAttempts']) is not int or not 1 <= batch['maxAttempts'] <= 64:
        raise ValueError('Invalid bounded attempt count')
    return request


def validate_binding(binding):
    if (binding.get('solverCommit') != COMMIT or binding.get('architecture') != 'sm_86'
            or binding.get('files', {}).get('pinning') != PIN
            or binding.get('files', {}).get('subset') != SUB):
        raise ValueError('Wrong installed candidate')


def run_batch(batch, invoke, work_range, publish, clock=time.monotonic):
    request = validate_batch(batch)
    deadline = clock() + SESSION_SECONDS
    state = dict(batchId=batch['batchId'], request=request, results=[], activeAttempt=None,
                 status='running', candidateRequiresCpuVerification=False,
                 grantsRangeCredit=False)
    publish(state)
    try:
        for offset in range(batch['maxAttempts']):
            if deadline - clock() < CALL_RESERVE_SECONDS:
                state['status'] = 'bounded-stop'
                break
            data = dict(request, attempt=request['attempt'] + offset)
            expected = work_range(data['stage'], data['attempt'])
            state['activeAttempt'] = data['attempt']
            publish(state)  # Must persist before invoking paid work.
            # A slow durable write must not consume the call's shutdown reserve.
            if deadline - clock() < CALL_RESERVE_SECONDS:
                state['neverStartedAttempt'] = data['attempt']
                state['activeAttempt'] = None
                state['status'] = 'bounded-stop'
                break
            result = invoke({'input': data})
            if (not isinstance(result, dict)
                    or any(result.get(k) != data[k] for k in
                           ('stage','manifestHash','attempt','kernelCommit'))
                    or result.get('workRange') != expected
                    or result.get('verified') is not False
                    or not isinstance(result.get('candidates'), list)
                    or len(result['candidates']) > 32
                    or any(not isinstance(c, str) or len(c.encode()) >= 16384
                           for c in result['candidates'])):
                raise ValueError('Unbound or malformed worker result')
            if result.get('status') != 'completed' or result.get('checkpoint') != 'range-complete':
                # Keep the active intent: failed/interrupted ranges need reconciliation.
                state['failedResult'] = result
                state['status'] = 'operator-reconciliation-required'
                break
            state['results'].append(result)
            state['activeAttempt'] = None
            publish(state)
            if result['candidates']:
                state['status'] = 'candidate'
                state['candidateRequiresCpuVerification'] = True
                break
        else:
            state['status'] = 'batch-complete'
    except Exception as error:
        state['status'] = 'operator-reconciliation-required'
        state['errorType'] = type(error).__name__
    publish(state)
    return state


def write_checkpoint(target, value):
    temporary = target.with_suffix('.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, sort_keys=True)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    temporary.replace(target)
    fd = os.open(target.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def main():
    import subprocess
    sys.path.insert(0, '/opt/qsb')
    import handler
    from search_ranges import work_range
    batch_path, target = map(Path, sys.argv[1:])
    batch_raw = batch_path.read_bytes()
    batch = json.loads(batch_raw)
    batch_hash = hashlib.sha256(batch_raw).hexdigest()
    request = validate_batch(batch)
    binding = handler.release_binding(); validate_binding(binding)
    handler.historical_handler.PINNED_KERNEL = COMMIT
    handler.historical_handler.validate_request(request)
    gpu = subprocess.check_output(['nvidia-smi','--query-gpu=name','--format=csv,noheader'], text=True).strip()
    if len(gpu.splitlines()) != 1 or 'A10G' not in gpu:
        raise ValueError('Exactly one A10G required')
    # Retained intent refuses restarts even when the last result is incomplete.
    with target.open('x') as stream:
        json.dump({'status':'intent','batchId':batch['batchId']}, stream)
        stream.flush(); os.fsync(stream.fileno())
    def publish(state):
        write_checkpoint(target, dict(state, binding=binding,
                         batchSha256=batch_hash))
    result = run_batch(batch, handler.handler, work_range, publish)
    return 2 if result['status'] == 'operator-reconciliation-required' else 0


if __name__ == '__main__':
    sys.exit(main())
