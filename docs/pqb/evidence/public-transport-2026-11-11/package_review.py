import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tarfile

root, output = map(Path, sys.argv[1:])
output.mkdir(parents=True, exist_ok=False)
external = []
archives = {}

def identity(path):
    return {'path': str(path.relative_to(root)), 'bytes': path.stat().st_size,
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

def copy(relative, target=None):
    source = root / relative
    destination = output / (target or relative)
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)

def archive(name, paths):
    members = []
    with (output / name).open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w|') as tar:
            for path in sorted(paths):
                info = tar.gettarinfo(str(path), arcname=str(path.relative_to(root)))
                info.uid = info.gid = 0
                info.uname = info.gname = ''
                with path.open('rb') as stream:
                    tar.addfile(info, stream)
                members.append(identity(path))
    archives[name] = members

for name in ['campaign.json', 'completion-receipt.json', 'final-audit.json', 'final_audit.py',
    'public-input.json', 'solve-config.json', 'state.json', 'reconciliation-final.json', 'package_review.py',
    'private-image.json', 'price-ami.json', 'instance-history.json', 'jobs-snapshot-143.json',
    'reference-native-requirements.txt', 'reference-native-runtime.json', 'reference-shim-runtime.json',
    'consumerOriginalAndRestoredTree.json']:
    if (root / name).exists():
        copy(name)
for path in sorted(root.glob('upstream-*.json')):
    copy(path.name)
for name in ['controller-tested-v2', 'controller-policy-fixed', 'controller-policy-restored', 'controller-reference-check']:
    copy(name + '/build-receipt.json')
    executable = root / name / 'controller.cjs'
    item = identity(executable)
    item['reason'] = 'Original compiled development controller retained locally; pinned source, build inputs and binary hash supplied'
    external.append(item)
for name in ['publisher/reconciliation-final.json', 'publisher/public-result.b64',
    'publisher/public-result.json.gz', 'publisher/ssm-intent.json', 'publisher/ssm-command.sh',
    'publisher/public/build-receipt.json', 'publisher/public/binding.json',
    'publisher/public/image.json', 'publisher/public/SHA256SUMS',
    'publisher/public/pqb-image-scan/image-scan.json',
    'controller-handover-intent.json', 'controller-handover-completion.json',
    'policy-restoration-handover.json', 'ci-initial-run-final.json', 'ci-initial-jobs-final.json',
    'ci-pqb-final-log.json', 'ci-reference-tools-jobs-final.json',
    'staging-deletion-intent.json']:
    copy(name)
for path in sorted(root.glob('ci-*.json')):
    if not (output / path.name).exists():
        copy(path.name)
provider = []
for path in (root / 'provider').glob('*.json'):
    if re.search(rb'(?:ASIA|AKIA)[A-Z0-9]{16}', path.read_bytes()):
        external.append(identity(path) | {'reason': 'Original CloudTrail record with temporary credential identifiers retained locally'})
    else:
        provider.append(path)
archive('provider-receipts.tar.gz', provider)
archive('cloudwatch.tar.gz', (root / 'cloudwatch').glob('*.json'))
control_files = []
for name in ['solve', 'solve-policy-fixed', 'solve-restored']:
    control_files.extend((root / name).glob('*.json'))
    control_files.extend((root / name / 'jobs').glob('*.json'))
control_files.extend(root.glob('solve*.log'))
control_files.extend(root.glob('stop-*.log'))
control_files.append(root / 'remove.log')
archive('controller-records.tar.gz', control_files)
archive('s3-objects.tar.gz', [p for p in (root / 's3').rglob('*') if p.is_file()])
rpc = []
for directory in [root / 'rpc', root / 'publisher/rpc']:
    rpc.extend(identity(p) for p in directory.iterdir() if p.is_file())
(output / 'operator-rpc-file-hashes.json').write_text(json.dumps(rpc, indent=2) + '\n')
image = next(x for x in json.loads((root / 'final-audit.json').read_bytes())['s3Objects'] if x['key'] == 'publisher/image.tar.gz')
external.append({'path': 'publisher/image.tar.gz', 'bytes': image['bytes'], 'sha256': image['sha256'],
    'reason': 'Exact private validation image archive retained locally, outside Git; private registry removed after assessment'})
files = [{'path': str(path.relative_to(output)), 'bytes': path.stat().st_size,
    'sha256': hashlib.sha256(path.read_bytes()).hexdigest()} for path in sorted(output.rglob('*')) if path.is_file()]
manifest = {'format': 'qsb-public-solve-review-package-v1', 'status': 'One public synthetic solve completed; cleanup independently verified; candidate HOLD',
    'files': files, 'archiveMembers': archives, 'externalOriginalsRetainedInCampaignDirectory': external,
    'operatorResponses': 'Wider operator RPC responses remain local; all hashes listed separately. Originals were not modified or deleted.',
    'extraction': 'Extract the four tar.gz files into one directory to restore original relative paths. Native public-result.json.gz is the original gzip JSON mapping of text receipts.',
    'imageSourceCommit': '4bfd8f1f7011331979f33b60bb8c6e379227ca16',
    'activeSolveControllerCommit': '04d6039a85f9fde145ea5540c874a4c27b5e9417',
    'consumerCommit': '276f2ae09d50ca44d46b035e45b6d0365802edcf',
    'consumerTreeAlsoAtOriginal81c060d': '37e3b41d7142001d2cdf676f1101489e9d6e50f4'}
(output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(files), 'archiveMembers': {k: len(v) for k, v in archives.items()},
    'bytes': sum(x['bytes'] for x in files), 'externalOriginals': len(external)}))
