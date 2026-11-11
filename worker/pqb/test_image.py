"""Offline checks of a built PQB candidate image: no GPU, no network.

    python3 worker/pqb/test_image.py IMAGE

They show the image is bound to its files and refuses bad requests, and that the compiled grinder
fails without a GPU instead of crediting a range. They do not show it computes anything correctly.
"""
import json
import subprocess
import sys

CHECK = r'''
import base64, hashlib, json, pathlib
import pqb_handler as h
b = h.release_binding()
assert b['status'] == 'HOLD' and len(b['solverCommit']) == 40
receipt = json.loads(pathlib.Path('build-receipt.json').read_text())
assert receipt['binarySha256'] == b['files']['grind'] == hashlib.sha256(pathlib.Path('grind').read_bytes()).hexdigest()
for name in ('licenses/pqb-LICENSE', 'licenses/pqb-THIRD_PARTY_NOTICES.md', 'licenses/LICENSES.md',
             'source/research/pqb-ranked/grind.cu', 'source/vendor/pqb/provenance.json'):
    assert pathlib.Path(name).is_file(), name
assert not pathlib.Path('/opt/qsb/cpu').exists()
raw = pathlib.Path('/fixture/pin.txt').read_bytes().replace(b'gate_bits 12\n', b'gate_bits 24\n')
req = {'protocol': 'pqb-v1', 'stage': 'pinning', 'attempt': 0, 'searchVersion': 'pqb-ranked-v1',
       'problemBase64': base64.b64encode(raw).decode(), 'problemSha256': hashlib.sha256(raw).hexdigest(),
       'manifestHash': 'cd' * 32, 'kernelCommit': b['solverCommit']}
for bad in (dict(req, kernelCommit='0' * 40), dict(req, seed='00'), dict(req, searchVersion='ranked-v2')):
    try:
        h.handler({'input': bad})
        raise SystemExit('accepted a bad request')
    except ValueError:
        pass
out = h.handler({'input': req})            # no GPU here: the real binary must fail, uncredited
assert out['status'] == 'failed' and out['checkpoint'] != 'range-complete' and out['candidates'] == [], out
print(json.dumps({'solverCommit': b['solverCommit'], 'binarySha256': receipt['binarySha256']}))
'''


def main():
    image = sys.argv[1]
    fixtures = __file__.rsplit('/worker/pqb/', 1)[0] + '/research/pqb-ranked/tests/fixtures'
    done = subprocess.run(['docker', 'run', '--rm', '--network', 'none', '--read-only', '--tmpfs', '/tmp',
                           '-v', fixtures + ':/fixture:ro', '--entrypoint', 'python3', image, '-c', CHECK],
                          capture_output=True, text=True)
    sys.stdout.write(done.stdout)
    sys.stderr.write(done.stderr)
    if done.returncode:
        sys.exit(done.returncode)
    json.loads(done.stdout.strip().splitlines()[-1])


if __name__ == '__main__':
    main()
