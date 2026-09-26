"""Prepare an exact-image descriptor proposal. This does not approve or enroll it."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from release_descriptor import descriptor

FILES = {'pinning', 'subset', 'handler.py', 'historical_handler.py', 'search_ranges.py'}
PIPELINE_KEYS = {'format', 'status', 'solverCommit', 'searchVersion',
                 'pinningUpstreamCommit', 'subsetUpstreamCommit',
                 'subsetSourceLockSha256', 'files'}


NVIDIA_ENTRYPOINT = ['/opt/nvidia/nvidia_entrypoint.sh']

def hex_value(value, length):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{%d}' % length, value) is not None


def proposal(pipeline_bytes, receipt_bytes, source_commit, image_digest, contract_bytes, *, target="generic", image_config=None):
    """Inputs must be extracted from the separately provenance-verified image."""
    pipeline = json.loads(pipeline_bytes)
    receipt = json.loads(receipt_bytes)
    if (not isinstance(pipeline, dict) or set(pipeline) not in (PIPELINE_KEYS, PIPELINE_KEYS | {'architecture'})
            or pipeline['format'] != 'qsb-combined-candidate-v1'
            or pipeline['status'] != 'HOLD' or pipeline['searchVersion'] != 'ranked-v2'
            or pipeline['solverCommit'] != source_commit
            or not hex_value(source_commit, 40)):
        raise ValueError('Invalid or mismatched combined pipeline')
    for field in ['pinningUpstreamCommit', 'subsetUpstreamCommit']:
        if not hex_value(pipeline[field], 40):
            raise ValueError('Invalid upstream identity')
    files = pipeline['files']
    if (not isinstance(files, dict) or set(files) != FILES
            or any(not hex_value(value, 64) for value in files.values())
            or not hex_value(pipeline['subsetSourceLockSha256'], 64)):
        raise ValueError('Invalid artifact inventory')
    if (not isinstance(receipt, dict)
            or receipt.get('binarySha256') != files['subset']
            or receipt.get('sourceLockSha256') != pipeline['subsetSourceLockSha256']):
        raise ValueError('Build receipt differs from installed pipeline')
    if 'architecture' in pipeline:
        arch=pipeline['architecture']
        if arch not in ('sm_86','sm_89') or receipt.get('architecture')!=arch or receipt.get('flags',[]).count('-arch='+arch)!=1:
            raise ValueError('Build architecture mismatch')
    if target not in ('generic', 'aws'):
        raise ValueError('Unknown release target')
    # The CUDA base image's entrypoint only prints a banner and execs its arguments, so the
    # Batch command still reaches aws_entrypoint.py. Both aws-v0.1.0 and the tested candidate
    # inherit it; any other entrypoint could intercept the command and stays refused.
    if target == 'aws':
        if pipeline.get('architecture') != 'sm_86':
            raise ValueError('AWS requires an explicit sm_86 binding')
        if (not isinstance(image_config, dict)
                or image_config.get('Cmd') != ['python3', 'aws_entrypoint.py']
                or image_config.get('Entrypoint') not in (None, [], NVIDIA_ENTRYPOINT)
                or image_config.get('WorkingDir') != '/opt/qsb'):
            raise ValueError('AWS runtime command/config mismatch')
    value = descriptor(source_commit, image_digest)
    # The combined worker echoes its own source commit, not an upstream lineage.
    value['kernelCommit'] = source_commit
    value['schemaVersion'] = 3
    contract = json.loads(contract_bytes)
    if not isinstance(contract, dict) or contract.get('searchVersion') != 'ranked-v2':
        raise ValueError('Invalid source search contract')
    canonical = json.dumps(contract, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
    value['searchContract'] = hashlib.sha256(canonical).hexdigest()
    return {'format': 'qsb-combined-descriptor-proposal-v1', 'status': 'HOLD',
            'solver': value,
            'binding': {'target': target,
                        'imageConfigSha256': hashlib.sha256(json.dumps(image_config, sort_keys=True, separators=(',', ':')).encode()).hexdigest() if image_config is not None else None,
                        'contractSourceCommit': source_commit,
                        'contractFileSha256': hashlib.sha256(contract_bytes).hexdigest(),
                        'pipelineSha256': hashlib.sha256(pipeline_bytes).hexdigest(),
                        'buildReceiptSha256': hashlib.sha256(receipt_bytes).hexdigest(),
                        'files': files,
                        'subsetSourceLockSha256': pipeline['subsetSourceLockSha256']},
            'remainingApproval': ['independent-final-review', 'native-sm86-correctness-and-matched-a10g-performance',
                                  'reviewed-publication-and-app-enrollment']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pipeline', type=Path, required=True)
    parser.add_argument('--build-receipt', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--image-digest', required=True)
    parser.add_argument('--target', choices=['generic', 'aws'], required=True)
    parser.add_argument('--image-config', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not hex_value(args.source_commit, 40):
        parser.error('An exact source commit is required')
    repo = Path(__file__).resolve().parents[1]
    contract = subprocess.check_output(['git', '-C', str(repo), 'show',
                                        args.source_commit + ':contracts/ranked-v2.json'])
    value = proposal(args.pipeline.read_bytes(), args.build_receipt.read_bytes(),
                     args.source_commit, args.image_digest, contract, target=args.target,
                     image_config=json.loads(args.image_config.read_text()) if args.image_config else None)
    # Never overwrite prior approval/evidence or emit an enrolled solver.json.
    with args.output.open('x') as output:
        output.write(json.dumps(value, indent=2) + '\n')


if __name__ == '__main__':
    main()
