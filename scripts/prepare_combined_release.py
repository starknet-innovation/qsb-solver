"""Verify provenance and extract a HOLD proposal from an immutable candidate image.

Read-only registry/container operations. No release publication, enrollment or GPU.
"""
import argparse
import base64
import json
from pathlib import Path
import re
import subprocess
import uuid
from combined_descriptor import hex_value, proposal

REPO = 'starknet-innovation/qsb-solver'
IMAGE_PREFIX = 'ghcr.io/' + REPO + '@'
EXTRACT = '''import base64,json,pathlib,handler
handler.release_binding()
root=pathlib.Path('/opt/qsb')
print(json.dumps({n:base64.b64encode((root/n).read_bytes()).decode() for n in ['pipeline.json','optimized-build-receipt.json']}))
'''


def prepare(image_digest, source_commit, candidate_tag, output, run=subprocess.run, *, target="generic"):
    if (not re.fullmatch(r'sha256:[a-f0-9]{64}', image_digest)
            or not hex_value(source_commit, 40)
            or not re.fullmatch(r'candidate-[a-zA-Z0-9][a-zA-Z0-9._-]*', candidate_tag)):
        raise ValueError('Exact image digest, source commit and candidate tag required')
    output = Path(output)
    output.mkdir(parents=False, exist_ok=False)
    image = IMAGE_PREFIX + image_digest
    ref = 'refs/tags/' + candidate_tag
    verify = ['gh', 'attestation', 'verify', 'oci://' + image, '--repo', REPO,
              '--source-digest', source_commit, '--source-ref', ref,
              '--signer-digest', source_commit, '--deny-self-hosted-runners',
              '--cert-identity', 'https://github.com/' + REPO + '/.github/workflows/candidate.yml@' + ref,
              '--format', 'json']
    try:
        checked = run(verify, check=True, capture_output=True, text=True, timeout=120)
    except subprocess.CalledProcessError as exc:
        (output / 'attestation-error.txt').write_text(exc.stderr or '')
        raise
    (output / 'attestation.json').write_text(checked.stdout)
    run(['docker', 'pull', '--platform', 'linux/amd64', image], check=True, timeout=600)
    config = None
    if target == 'aws':
        inspected = run(['docker', 'image', 'inspect', '--format', '{{json .Config}}', image],
                        check=True, capture_output=True, text=True, timeout=30)
        config = json.loads(inspected.stdout)
        (output / 'image-config.json').write_text(inspected.stdout)
    container_name = 'qsb-release-extract-' + uuid.uuid4().hex
    try:
        extracted = run(['docker', 'run', '--rm', '--name', container_name,
                         '--platform', 'linux/amd64', '--network', 'none',
                         '--read-only', '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges',
                         '--entrypoint', 'python3', image, '-c', EXTRACT],
                        check=True, capture_output=True, text=True, timeout=90)
    finally:
        # Terminating a Docker client does not necessarily terminate its container.
        run(['docker', 'rm', '--force', container_name], check=False,
            capture_output=True, timeout=30)
    raw = json.loads(extracted.stdout)
    if set(raw) != {'pipeline.json', 'optimized-build-receipt.json'}:
        raise ValueError('Unexpected extracted inventory')
    contents = {name: base64.b64decode(value, validate=True) for name, value in raw.items()}
    repo = Path(__file__).resolve().parents[1]
    contract = run(['git', '-C', str(repo), 'show', source_commit + ':contracts/ranked-v2.json'],
                   check=True, capture_output=True, timeout=30).stdout
    result = proposal(contents['pipeline.json'], contents['optimized-build-receipt.json'],
                      source_commit, image_digest, contract, target=target, image_config=config)
    for name, data in contents.items():
        (output / name).write_bytes(data)
    (output / 'descriptor-proposal.json').write_text(json.dumps(result, indent=2) + '\n')
    (output / 'preparation.json').write_text(json.dumps({
        'status': 'HOLD', 'image': image, 'sourceCommit': source_commit,
        'candidateTag': candidate_tag, 'publicationPerformed': False,
        'enrollmentPerformed': False}, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', choices=['generic', 'aws'], required=True)
    parser.add_argument('--image-digest', required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--candidate-tag', required=True)
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    prepare(args.image_digest, args.source_commit, args.candidate_tag, args.output_directory, target=args.target)


if __name__ == '__main__':
    main()
