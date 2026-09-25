"""Validate a collected public archive without granting search coverage credit."""
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import re

MAX_ENCODED = 2_000_000
MAX_DECODED = 8_000_000
FILES = {'deadline.txt', 'gpu.txt', 'gate.log', 'exit-code.txt', 'result.json'}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON key')
        result[key] = value
    return result


def decode_archive(encoded, metadata):
    if (set(metadata) != {'bytes', 'sha256'}
            or type(metadata['bytes']) is not int
            or not 0 < metadata['bytes'] <= MAX_ENCODED
            or not re.fullmatch('[0-9a-f]{64}', metadata['sha256'])):
        raise ValueError('Invalid result metadata')
    if len(encoded) != metadata['bytes'] or hashlib.sha256(encoded).hexdigest() != metadata['sha256']:
        raise ValueError('Incomplete or corrupted result collection')
    compressed = base64.b64decode(encoded, validate=True)
    with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
        raw = stream.read(MAX_DECODED + 1)
    if len(raw) > MAX_DECODED:
        raise ValueError('Decoded result exceeds bound')
    files = json.loads(raw, object_pairs_hook=unique_object)
    if (not isinstance(files, dict) or set(files) != FILES
            or any(not isinstance(v, str) for v in files.values())):
        raise ValueError('Unexpected public result files')
    return files


def bind_result(files, batch_raw, validate_batch, validate_binding, work_range):
    batch = json.loads(batch_raw, object_pairs_hook=unique_object)
    request = validate_batch(batch)
    result = json.loads(files['result.json'], object_pairs_hook=unique_object)
    validate_binding(result['binding'])
    if (result.get('batchSha256') != hashlib.sha256(batch_raw).hexdigest()
            or result.get('batchId') != batch['batchId']
            or result.get('request') != request
            or result.get('grantsRangeCredit') is not False):
        raise ValueError('Result does not bind submitted public batch')
    rows = result.get('results')
    if not isinstance(rows, list) or len(rows) > batch['maxAttempts']:
        raise ValueError('Invalid result inventory')
    for offset, row in enumerate(rows):
        attempt = request['attempt'] + offset
        if (not isinstance(row, dict) or type(row.get('attempt')) is not int
                or row['attempt'] != attempt
                or any(row.get(k) != request[k] for k in ('stage','manifestHash','kernelCommit'))
                or row.get('workRange') != work_range(request['stage'], attempt)
                or row.get('status') != 'completed' or row.get('checkpoint') != 'range-complete'
                or row.get('verified') is not False
                or not isinstance(row.get('candidates'), list)
                or len(row['candidates']) > 32
                or any(not isinstance(c, str) or len(c.encode()) >= 16384 for c in row['candidates'])
                or (row['candidates'] and offset != len(rows)-1)):
            raise ValueError('Unbound, skipped or malformed result row')
    status = result.get('status')
    if status not in {'batch-complete','bounded-stop','candidate','operator-reconciliation-required','running'}:
        raise ValueError('Unknown session outcome')
    clean = status in {'batch-complete','bounded-stop','candidate'}
    if clean and any(key in result for key in ('failedResult', 'errorType')):
        raise ValueError('Failure evidence contradicts clean outcome')
    if 'neverStartedAttempt' in result and (
            status != 'bounded-stop'
            or type(result['neverStartedAttempt']) is not int
            or result['neverStartedAttempt'] != request['attempt'] + len(rows)
            or len(rows) >= batch['maxAttempts']
            or result.get('activeAttempt') is not None):
        raise ValueError('Invalid never-started attempt')
    if clean and (result.get('activeAttempt') is not None or files['exit-code.txt'].strip() != '0'):
        raise ValueError('Contradictory clean completion')
    hits = bool(rows and rows[-1]['candidates'])
    if clean and ((status == 'candidate') != hits or result.get('candidateRequiresCpuVerification') != hits):
        raise ValueError('Contradictory candidate outcome')
    if status == 'batch-complete' and len(rows) != batch['maxAttempts']:
        raise ValueError('Incomplete batch claims completion')
    return dict(status=status, completedWorkerRows=len(rows),
                candidateRequiresCpuVerification=hits, grantsRangeCredit=False,
                requiresReconciliation=not clean)


def assemble_chunks(chunks, metadata):
    """Offsets and exact lengths exclude gaps, overlaps, duplicates and stale tails."""
    if type(metadata.get('bytes')) is not int or not 0 < metadata['bytes'] <= MAX_ENCODED:
        raise ValueError('Invalid collection length')
    position = 0
    result = bytearray()
    for offset, data in chunks:
        if type(offset) is not int or offset != position or not isinstance(data, bytes) or not data:
            raise ValueError('Noncontiguous public chunks')
        result.extend(data)
        position += len(data)
        if position > metadata['bytes']:
            raise ValueError('Collection exceeds expected size')
    encoded = bytes(result)
    decode_archive(encoded, metadata)
    return encoded


def persist_collection(directory, encoded, metadata, batch_raw, validate_batch, validate_binding, work_range):
    """New evidence directory only; a receipt is written last after file fsyncs."""
    import os
    files = decode_archive(encoded, metadata)
    summary = bind_result(files, batch_raw, validate_batch, validate_binding, work_range)
    directory = Path(directory)
    directory.mkdir()  # Never overwrite or silently repair a partial collection.
    parent_fd = os.open(directory.parent, os.O_RDONLY)
    try:
        os.fsync(parent_fd)  # Persist the new directory entry as well as its contents.
    finally:
        os.close(parent_fd)
    def write(name, data):
        with (directory / name).open('xb') as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
    write('public-result.b64', encoded)
    write('batch.json', batch_raw)
    for name, value in files.items():
        write(name, value.encode())
    hashes = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in directory.iterdir()}
    receipt = dict(summary, archive=metadata, files=hashes)
    write('collection-receipt.json', (json.dumps(receipt, sort_keys=True)+'\n').encode())
    fd = os.open(directory, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)
    return receipt
