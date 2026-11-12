"""Verify every OCI blob, retain the exact publishable manifest and configuration.

No registry access or publication. The archive and manifest need independent GitHub
attestation verification before native execution or subsequent digest-preserving copy.
"""
import hashlib
import json
from pathlib import Path
import re
import tarfile
import sys


def inspect(archive):
    metadata = {}
    seen = set()
    with tarfile.open(archive) as tar:
        for member in tar:
            name = member.name.rstrip('/')
            if member.isdir():
                continue
            if not member.isfile() or name in seen or name.startswith('/') or '..' in Path(name).parts:
                raise ValueError('Unsafe or duplicate OCI member')
            seen.add(name)
            if name in ('index.json', 'oci-layout'):
                if member.size > 1024 * 1024:
                    raise ValueError('Oversized OCI metadata')
                metadata[name] = tar.extractfile(member).read()
            elif re.fullmatch('blobs/sha256/[a-f0-9]{64}', name):
                stream = tar.extractfile(member)
                digest = hashlib.sha256()
                keep = member.size <= 8 * 1024 * 1024
                parts = []
                for data in iter(lambda: stream.read(1024 * 1024), b''):
                    digest.update(data)
                    if keep:
                        parts.append(data)
                if digest.hexdigest() != name.split('/')[-1]:
                    raise ValueError('OCI blob hash mismatch')
                if keep:
                    metadata[name] = b''.join(parts)
            else:
                raise ValueError('Unexpected OCI archive member: ' + name)
    if json.loads(metadata['oci-layout']) != {'imageLayoutVersion': '1.0.0'}:
        raise ValueError('Unsupported OCI layout')
    roots = json.loads(metadata['index.json'])['manifests']
    if len(roots) != 1:
        raise ValueError('Expected one named root image')
    root = roots[0]
    def blob(desc):
        digest = desc['digest']
        if not re.fullmatch('sha256:[a-f0-9]{64}', digest):
            raise ValueError('Invalid OCI digest')
        key = 'blobs/sha256/' + digest[7:]
        raw = metadata[key]
        if len(raw) != desc['size']:
            raise ValueError('OCI descriptor size mismatch')
        return raw
    raw = blob(root)
    index = json.loads(raw)
    platforms = [m for m in index['manifests'] if m.get('platform') == {'architecture': 'amd64', 'os': 'linux'}]
    if len(platforms) != 1:
        raise ValueError('Expected exactly one linux/amd64 platform')
    manifest = json.loads(blob(platforms[0]))
    for layer in manifest['layers']:
        if 'blobs/sha256/' + layer['digest'].removeprefix('sha256:') not in seen:
            raise ValueError('Missing image layer')
    config_raw = blob(manifest['config'])
    config = json.loads(config_raw)
    if (config['architecture'] != 'amd64' or config['os'] != 'linux'
            or config['config'].get('WorkingDir') != '/opt/qsb-pqb'
            or config['config'].get('Cmd') != ['python3', 'aws_entrypoint.py']):
        raise ValueError('Unexpected PQB runtime config')
    return dict(format='qsb-pqb-oci-identity-v1', status='HOLD', imageDigest=root['digest'],
                platformDigest=platforms[0]['digest'], configDigest=manifest['config']['digest']), raw, config_raw


def main():
    archive, output = map(Path, sys.argv[1:])
    identity, manifest, config = inspect(archive)
    for name, raw in [('oci-identity.json', (json.dumps(identity, indent=2)+'\n').encode()),
                      ('image-manifest.json', manifest), ('image-config.json', config)]:
        with (output / name).open('xb') as file:
            file.write(raw)
    print(json.dumps(identity))


if __name__ == '__main__':
    main()
