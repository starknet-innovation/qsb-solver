"""Prepare a HOLD proposal from retained PQB evidence, never an enrolled solver.json.

This checks recorded identities offline. It does not verify registry availability,
GitHub build provenance, GPU correctness, or permission to publish/adopt an image.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RUNTIME_INPUTS = (
    'worker/pqb/Dockerfile', 'worker/pqb/build.py', 'worker/pqb/bind.py',
    'worker/pqb/pqb_handler.py', 'worker/pqb/pqb_ranges.py',
    'worker/pqb/aws_handler.py', 'worker/aws/entrypoint.py',
    'research/pqb-ranked/grind.cu', 'research/pqb-ranked/source-lock.json',
    'vendor/pqb/grinder/grind.cu', 'vendor/pqb/grinder/common.cuh',
    'vendor/pqb/grinder/ptx_field.cuh', 'vendor/pqb/LICENSE',
    'vendor/pqb/grinder/README.md', 'vendor/pqb/provenance.json',
    'vendor/pqb/THIRD_PARTY_NOTICES.md', 'LICENSES.md',
)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def source(commit, path):
    if not isinstance(commit, str) or not re.fullmatch('[a-f0-9]{40}', commit):
        raise ValueError('An exact source commit is required')
    return subprocess.check_output(['git', '-C', str(ROOT), 'show', commit + ':' + path])


def contract_hash(raw, ranges):
    contract = json.loads(raw)
    # Execute only committed local partition code, never data from an image or receipt.
    namespace = {}
    exec(compile(ranges, 'committed-pqb_ranges.py', 'exec'), namespace)
    if (contract.get('searchVersion') != 'pqb-ranked-v2'
            or namespace['VERSION'] != 'pqb-ranked-v2'
            or not contract.get('cases') or not contract.get('invalid')):
        raise ValueError('Invalid PQB contract')
    for case in contract['cases']:
        if namespace['work_range'](case['stage'], case['attempt']) != case['range']:
            raise ValueError('PQB contract vector mismatch')
    for case in contract['invalid']:
        try:
            namespace['work_range'](case['stage'], case['attempt'])
        except ValueError:
            continue
        raise ValueError('PQB invalid vector accepted')
    # Python must preserve the deliberately invalid floating token 1.0.
    return sha(json.dumps(contract, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode())


def prepare(evidence, review_commit):
    evidence = Path(evidence)
    manifest_raw = (evidence / 'manifest.json').read_bytes()
    manifest = json.loads(manifest_raw)
    if manifest.get('format') != 'qsb-public-solve-review-package-v1':
        raise ValueError('Unknown evidence format')
    files = {row['path']: row for row in manifest['files']}
    if len(files) != len(manifest['files']):
        raise ValueError('Duplicate evidence path')
    for name, row in files.items():
        path = (evidence / name).resolve()
        if not path.is_relative_to(evidence.resolve()) or path.is_symlink():
            raise ValueError('Unsafe evidence path')
        raw = path.read_bytes()
        if len(raw) != row['bytes'] or sha(raw) != row['sha256']:
            raise ValueError('Evidence hash mismatch: ' + name)

    def read(name):
        if name not in files:
            raise ValueError('Unbound evidence: ' + name)
        return json.loads((evidence / name).read_bytes())

    image = read('private-image.json')
    binding = read('publisher/public/binding.json')
    receipt = read('publisher/public/build-receipt.json')
    inspections = read('publisher/public/image.json')
    commit = image['sourceCommit']
    digest = image['image'].split('@')[-1]
    if (image.get('status') != 'private-validation-only'
            or manifest.get('imageSourceCommit') != commit
            or not re.fullmatch('sha256:[0-9a-f]{64}', digest)
            or sha(image['manifest'].encode()) != digest[7:]):
        raise ValueError('Registry index identity mismatch')
    index = json.loads(image['manifest'])
    platforms = [m for m in index['manifests'] if m.get('platform') == {'architecture': 'amd64', 'os': 'linux'}]
    if len(platforms) != 1:
        raise ValueError('Expected one linux/amd64 manifest')
    if (binding != image['binding'] or binding.get('format') != 'qsb-pqb-candidate-v1'
            or binding.get('status') != 'HOLD' or binding.get('solverCommit') != commit
            or binding.get('cudaArchitecture') != '86'
            or set(binding.get('files', {})) != {'grind', 'pqb_handler.py', 'pqb_ranges.py'}
            or any(not re.fullmatch('[a-f0-9]{64}', value) for value in binding['files'].values())):
        raise ValueError('Invalid PQB image binding')
    lock_raw = source(commit, 'research/pqb-ranked/source-lock.json')
    lock = json.loads(lock_raw)
    if (receipt.get('format') != 'qsb-pqb-build-receipt-v1' or receipt.get('status') != 'HOLD'
            or receipt.get('binarySha256') != binding['files']['grind']
            or receipt.get('sourceLockSha256') != sha(lock_raw) or receipt.get('sourceLock') != lock
            or receipt.get('cudaArchitecture') != '86'
            or receipt.get('flags') != ['-O3', '-std=c++17', '-arch=sm_86', '-I', '/src/vendor/pqb/grinder']):
        raise ValueError('Build receipt differs from source/binary identity')
    for path, expected in lock['sources'].items():
        if sha(source(commit, path)) != expected:
            raise ValueError('Source-lock mismatch: ' + path)
    provenance = json.loads(source(commit, 'vendor/pqb/provenance.json'))
    if (lock['upstream']['repository'] != provenance['repository']
            or lock['upstream']['commit'] != provenance['commit']
            or sha(source(commit, 'vendor/pqb/' + lock['upstream']['adaptedFrom'])) != lock['upstream']['adaptedFromSha256']):
        raise ValueError('Upstream provenance mismatch')
    for path, expected in provenance['files'].items():
        if sha(source(commit, 'vendor/pqb/' + path)) != expected:
            raise ValueError('Vendor hash mismatch: ' + path)
    for name in ('pqb_handler.py', 'pqb_ranges.py'):
        if sha(source(commit, 'worker/pqb/' + name)) != binding['files'][name]:
            raise ValueError('Installed Python source differs: ' + name)
    if not isinstance(inspections, list) or len(inspections) != 1:
        raise ValueError('Expected one image inspection')
    config = inspections[0]['Config']
    if (inspections[0].get('Id') != image.get('imageId')
            or inspections[0]['Architecture'] != 'amd64' or inspections[0]['Os'] != 'linux'
            or config.get('Cmd') != ['python3', 'aws_entrypoint.py']
            or config.get('WorkingDir') != '/opt/qsb-pqb'
            or config.get('Entrypoint') not in (None, [], ['/opt/nvidia/nvidia_entrypoint.sh'])):
        raise ValueError('AWS runtime mismatch')
    contract = source(commit, 'contracts/pqb-ranked-v2.json')
    contract_digest = contract_hash(contract, source(commit, 'worker/pqb/pqb_ranges.py'))
    solver = dict(schemaVersion=3, id='pqb-ranked-v2-' + commit[:12] + '-' + digest[7:19],
                  protocol='pqb-v1', generatorCommit=lock['upstream']['commit'], searchVersion='pqb-ranked-v2',
                  searchContract=contract_digest, solverRepository='https://github.com/starknet-innovation/qsb-solver',
                  solverCommit=commit, kernelCommit=commit,
                  image='ghcr.io/starknet-innovation/qsb-solver@' + digest)
    drift = []
    for path in RUNTIME_INPUTS:
        before, after = sha(source(commit, path)), sha(source(review_commit, path))
        if before != after:
            drift.append(dict(path=path, imageSourceSha256=before, reviewedSourceSha256=after))
    return dict(format='qsb-pqb-descriptor-proposal-v1', status='HOLD',
                imageReferenceStatus='prospective-unpublished', publicationVerified=False,
                enrollmentApproved=False, solver=solver,
                binding=dict(target='aws-sm86', evidenceManifestSha256=sha(manifest_raw),
                             evidenceFilesChecked=len(files), contractFileSha256=sha(contract),
                             imageSourceCommit=commit, reviewedSourceCommit=review_commit,
                             amd64ManifestDigest=platforms[0]['digest'], privateValidationImage=image['image'],
                             sourceLockSha256=sha(lock_raw), files=binding['files'], runtimeInputDrift=drift),
                remainingGates=['refresh-image-with-reviewed-parser-fix',
                                'qualify-exact-new-image-and-review-evidence-applicability',
                                'authorized-publication-and-verified-build-provenance',
                                'regenerate-descriptor-from-published-artifact',
                                'separate-explicit-app-enrollment-and-deployment-review'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--review-commit', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    value = prepare(args.evidence, args.review_commit)
    with args.output.open('x') as output:
        output.write(json.dumps(value, indent=2) + '\n')


if __name__ == '__main__':
    main()
