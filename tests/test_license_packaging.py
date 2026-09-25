"""Notice retention checks; no GPU, network, provider calls or legal conclusions."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROFILES = {
    'historical': {
        '/opt/qsb/licenses/challenge-LICENSE': 'vendor/challenge/LICENSE',
        '/opt/qsb/licenses/pinning-COPYING': 'vendor/challenge/candidates/pinning/COPYING',
        '/opt/qsb/licenses/subset-COPYING': 'vendor/challenge/candidates/subset/COPYING',
        '/opt/qsb/licenses/LICENSES.md': 'LICENSES.md',
        '/opt/qsb/source/pinning/COPYING': 'vendor/challenge/candidates/pinning/COPYING',
        '/opt/qsb/source/subset/COPYING': 'vendor/challenge/candidates/subset/COPYING',
        '/opt/qsb/source/pinning/LeafRecovery.cuh': 'vendor/challenge/candidates/pinning/LeafRecovery.cuh',
        '/opt/qsb/source/pinning/GPUMath.h': 'vendor/challenge/candidates/pinning/GPUMath.h',
        '/opt/qsb/source/subset/GPUHash.h': 'vendor/challenge/candidates/subset/GPUHash.h',
        '/opt/qsb/source/build/prepare_kernels.py': 'worker/prepare_kernels.py',
        '/opt/qsb/source/build/Dockerfile': 'worker/Dockerfile',
    },
    'optimized': {
        '/opt/qsb-validation/licenses/subset-COPYING': 'vendor/challenge/candidates/subset/COPYING',
        '/opt/qsb-validation/licenses/optimized-subset-LICENSE': 'research/optimized-subset/LICENSE',
        '/opt/qsb-validation/licenses/LICENSES.md': 'LICENSES.md',
        '/opt/qsb-validation/candidate/source/LICENSE': 'research/optimized-subset/LICENSE',
        '/opt/qsb-validation/candidate/source/subset/GPUMath.h': 'research/optimized-subset/subset/GPUMath.h',
        '/opt/qsb-validation/candidate/source/subset/GPUHash.h': 'research/optimized-subset/subset/GPUHash.h',
        '/opt/qsb-validation/source-build/build.py': 'worker/optimized/build.py',
        '/opt/qsb-validation/source-build/Dockerfile': 'worker/optimized/Dockerfile',
        '/opt/qsb-validation/source-build/source-lock.json': 'worker/optimized/source-lock.json',
    },
}


def check_image(image, profile):
    paths = PROFILES[profile]
    code = ('import hashlib,json,sys; from pathlib import Path; '
            'print(json.dumps({p:hashlib.sha256(Path(p).read_bytes()).hexdigest() '
            'for p in json.loads(sys.argv[1])}))')
    actual = json.loads(subprocess.check_output([
        'docker', 'run', '--rm', '--network', 'none', '--read-only', '--cap-drop', 'ALL',
        '--security-opt', 'no-new-privileges', '--entrypoint', 'python3', image,
        '-c', code, json.dumps(list(paths)),
    ], text=True, timeout=60))
    expected = {p: hashlib.sha256((ROOT / source).read_bytes()).hexdigest()
                for p, source in paths.items()}
    if actual != expected:
        raise AssertionError('Image license/source notices do not match repository inputs')
    print(json.dumps({'profile': profile, 'matchedFiles': len(paths), 'gpuExecution': False}))


class LicensePackagingTests(unittest.TestCase):
    def test_repository_notices_preserved(self):
        for profile in PROFILES.values():
            for source in profile.values():
                self.assertTrue((ROOT / source).is_file(), source)
        for track in ('pinning', 'subset'):
            self.assertIn('GNU GENERAL PUBLIC LICENSE',
                          (ROOT / f'vendor/challenge/candidates/{track}/COPYING').read_text())
        for source in ('vendor/challenge/LICENSE', 'research/optimized-subset/LICENSE'):
            self.assertIn('Apache License', (ROOT / source).read_text())
        for source in ('vendor/challenge/candidates/pinning/GPUMath.h',
                       'research/optimized-subset/subset/GPUMath.h'):
            notice = (ROOT / source).read_text()
            self.assertIn('Copyright (c) 2019 Jean Luc PONS', notice)
            self.assertIn('GNU General Public License', notice)


if __name__ == '__main__':
    if '--image' in sys.argv:
        parser = argparse.ArgumentParser()
        parser.add_argument('--image', required=True)
        parser.add_argument('--profile', required=True, choices=PROFILES)
        args = parser.parse_args()
        check_image(args.image, args.profile)
    else:
        unittest.main()
