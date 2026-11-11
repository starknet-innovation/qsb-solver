import base64
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
state_dir = root / 'solve-restored'
state = json.loads((state_dir / 'state.json').read_bytes())
assert state['status'] == 'solved-public' and len(state['solutions']) == 3 and not state['slots']
jobs = {j['jobId']: j for j in json.loads((root / 'jobs-snapshot-143.json').read_bytes())}
assert len(jobs) == state['job']['gpuSubmissions'] == len(state['observations']) == 143
assert state['job']['gpuBudgetReservedSeconds'] == 900 * len(jobs)
intents = {}
for name in ('solve', 'solve-policy-fixed', 'solve-restored'):
    for path in (root / name / 'jobs').glob('*-intent.json'):
        intent = json.loads(path.read_bytes())
        key = intent['slot']['identity']['jobName']
        assert key not in intents
        intents[key] = (intent, str(path.relative_to(root)))
assert len(intents) == len(jobs)
assert sorted(i['reserved'] for i, _ in intents.values()) == list(range(900, 900 * (len(jobs) + 1), 900))
stages = {name: Counter() for name in ('pinning', 'round1', 'round2')}
records = []
hardware = []
native_checks = {name: json.loads((root / ('upstream-native-final-' + name + '.json')).read_bytes()) for name in stages}
for observation in state['observations']:
    identifier = observation['id']
    record = json.loads((state_dir / 'jobs' / (identifier + '.json')).read_bytes())
    slot, result = record['slot'], record['result']
    identity = slot['identity']
    intent, intent_path = intents[identity['jobName']]
    assert intent['slot']['identity'] == identity
    wire = (root / 's3' / identity['inputKey']).read_bytes()
    assert hashlib.sha256(wire).hexdigest() == identity['inputSha256']
    assert json.dumps({'input': intent['input']}, separators=(',', ':'), ensure_ascii=False).encode() == wire
    public_request = json.loads(wire)['input']
    assert hashlib.sha256(base64.b64decode(public_request['problemBase64'])).hexdigest() == public_request['problemSha256']
    provider = jobs[identifier]
    assert (provider['jobName'], provider['jobQueue'], provider['jobDefinition'], provider['container']['image']) == (
        identity['jobName'], identity['queue'], identity['definition'], state['config']['image'])
    stage = stages[slot['stage']]
    stage['submissions'] += 1
    stage['cancellationRequests'] += bool(slot.get('cancellation'))
    if result['status'] == 'COMPLETED':
        assert provider['status'] == 'SUCCEEDED'
        output = result['output']
        original = json.loads((root / 's3/outputs' / (identifier + '.json')).read_bytes())
        assert original['jobId'] == identifier and original['inputSha256'] == identity['inputSha256']
        assert original['output'] == output
        assert output['status'] == 'completed' and output['checkpoint'] == 'range-complete'
        stage['completed'] += 1
        stage['trials'] += output['trials']
        stage['gateHits'] += output['gateHits']
        stage['candidates'] += len(output['candidates'])
        stage['workerElapsedSeconds'] += output['elapsedSeconds']
        stage['entrypointExecutionSeconds'] += result['executionTime'] / 1000
        log = json.loads((root / 'cloudwatch' / (identifier + '.json')).read_bytes())['log']
        messages = [e['message'] for e in log['data']['events']]
        text = '\n'.join(messages)
        capabilities = re.findall(r'^Cap\w+:\s*(\w+)', text, re.M)
        assert len(capabilities) == 5 and all(int(c, 16) == 0 for c in capabilities)
        assert re.findall(r'^NoNewPrivs:\s*(\d+)', text, re.M) == ['1']
        gpus = [m for m in messages if m.startswith('NVIDIA A10G, GPU-')]
        assert len(gpus) == 1
        summaries = [json.loads(m) for m in messages if m.startswith('{')]
        assert any(m.get('jobId') == identifier and m.get('status') == 'completed' for m in summaries)
        hardware.append({'jobId': identifier, 'gpu': gpus[0], 'zeroCapabilities': True, 'noNewPrivs': True,
            'terminalSummaryPresent': True})
    else:
        assert result['status'] == 'FAILED' and provider['status'] == 'FAILED' and slot.get('cancellation')
        assert 'cancellation' in provider.get('statusReason', '')
        stage['cancelledTerminal'] += 1
        stage['cancelledBeforeStart'] += not bool(provider.get('startedAt'))
    records.append({'jobId': identifier, 'stage': slot['stage'], 'attempt': slot['attempt'],
        'inputSha256': identity['inputSha256'], 'problemSha256': public_request['problemSha256'],
        'originalIntent': intent_path, 'reservationSeconds': intent['reserved'],
        'terminalStatus': provider['status'], 'cancellationRequested': bool(slot.get('cancellation'))})
for name, stage in stages.items():
    checked = native_checks[name]
    assert checked['completedUnits'] == stage['completed'] and not checked['otherProblemJobsNotChecked']
    assert checked['curveBackend']['implementation'] == 'native-coincurve'
    stage['upstreamFullCandidates'] = sum(r['checks']['full_solutions'] for r in checked['records'])
    assert sum(r['checks']['checked'] for r in checked['records']) == stage['candidates']
history = json.loads((root / 'instance-history.json').read_bytes())
price = 1.123
costs = []
for identifier, entry in history.items():
    instance = entry['latest']
    assert instance['InstanceType'] == 'g5.xlarge' and instance['ImageId'] == 'ami-034c2d44a0a1d5e82'
    match = re.search(r'\((20\d\d-\d\d-\d\d \d\d:\d\d:\d\d) GMT\)', instance['StateTransitionReason'])
    assert match
    start = datetime.fromisoformat(instance['LaunchTime'])
    shutdown = datetime.strptime(match[1], '%Y-%m-%d %H:%M:%S').replace(tzinfo=timezone.utc)
    seconds = (shutdown - start).total_seconds()
    assert seconds > 0
    costs.append({'instanceId': identifier, 'launchTime': start.isoformat(), 'providerShutdownTransition': shutdown.isoformat(),
        'allocatedSeconds': seconds, 'estimatedBilledSecondsWith60sMinimum': max(60, seconds),
        'estimatedComputeUsd': max(60, seconds) * price / 3600, 'originalReceipts': entry['receipts']})
publisher = json.loads((root / 'publisher/reconciliation-final.json').read_bytes())['structuredContent']['return_value']['instance']
shutdown = datetime.strptime(re.search(r'\((.*?) GMT\)', publisher['StateTransitionReason'])[1], '%Y-%m-%d %H:%M:%S').replace(tzinfo=timezone.utc)
publisher_seconds = (shutdown - datetime.fromisoformat(publisher['LaunchTime'])).total_seconds()
started = datetime.fromisoformat(state['startedAt'].replace('Z', '+00:00'))
finished = datetime.fromisoformat(state['finishedAt'].replace('Z', '+00:00'))
listing_path = sorted((root / 'provider').glob('s3-list-*.json'))[-1]
listing = json.loads(listing_path.read_bytes())['structuredContent']['return_value']['listing']
objects = []
expected_archive = next(line.split()[0] for line in (root / 'publisher/public/SHA256SUMS').read_text().splitlines() if line.split()[1] == 'image.tar.gz')
for obj in listing['Contents']:
    path = root / 'publisher/image.tar.gz' if obj['Key'] == 'publisher/image.tar.gz' else root / 's3' / obj['Key']
    assert path.stat().st_size == obj['Size']
    sha, md5 = hashlib.sha256(), hashlib.md5()
    with path.open('rb') as stream:
        while chunk := stream.read(8 * 1024 * 1024):
            sha.update(chunk)
            md5.update(chunk)
    etag = obj['ETag'].strip('"')
    if re.fullmatch(r'[a-f0-9]{32}', etag):
        assert md5.hexdigest() == etag
    if obj['Key'] == 'publisher/image.tar.gz':
        assert sha.hexdigest() == expected_archive
    objects.append({'key': obj['Key'], 'bytes': obj['Size'], 'sha256': sha.hexdigest(), 'etag': obj['ETag']})
assert len(objects) == 266
result = {'format': 'qsb-public-solve-final-audit-v1', 'checkedAt': datetime.now(timezone.utc).isoformat(),
    'auditScriptSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'status': state['status'],
    'startedAt': state['startedAt'], 'finishedAt': state['finishedAt'], 'publicSolveWallSeconds': (finished - started).total_seconds(),
    'submissions': len(jobs), 'reservedGpuSeconds': state['job']['gpuBudgetReservedSeconds'], 'stages': stages,
    'batchInstances': len(costs), 'batchEstimatedComputeUsd': sum(c['estimatedComputeUsd'] for c in costs),
    'publisherInstance': publisher['InstanceId'], 'publisherSeconds': publisher_seconds,
    'publisherEstimatedComputeUsd': publisher_seconds * price / 3600,
    'totalEstimatedComputeUsd': sum(c['estimatedComputeUsd'] for c in costs) + publisher_seconds * price / 3600,
    'priceUsdPerG5XlargeHour': price, 'priceSnapshot': 'price-ami.json', 'providerBillingRead': False,
    'excludedCosts': 'EBS, IPv4, S3, ECR, network and other services', 'instanceCosts': costs,
    'requestIdentityAudit': records, 'completedHardwareAudit': hardware, 's3Objects': objects,
    'limits': 'One public synthetic solve; development orchestration with real consumer Batch/S3/CPU modules; no served coordinator, wallet, consensus, miner or broadcast execution'}
with (root / 'final-audit.json').open('x') as stream:
    json.dump(result, stream, indent=2)
    stream.write('\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('instanceCosts', 'requestIdentityAudit', 'completedHardwareAudit', 's3Objects')}))
