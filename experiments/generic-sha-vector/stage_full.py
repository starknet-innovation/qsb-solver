"""Prepare a bounded SSM handoff from committed public sources and frozen CI bytes."""
import base64
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys
import zlib

ROOT=Path(__file__).resolve().parents[2]
ZIP_SHA='5e9405ab2f75ae14499d4e0cb4a473eba5bc5699b278a580ba97adc914f67fc3'
BINARIES={'baseline':'8664f41f3deeeb91b3d189db3df469570c83e90610e4b54a955e2a625486606c',
          'candidate':'0fe47c3bd6b5b3671f02af242095922acd418ea5ab7c2f13647b0b386782ea7b',
          'candidate-trace':'42ad9574cef271c80181ece261d680fe771f4c21a383c5c72570f6e8f1d08018'}

def payload(commit):
    files={}
    for name in ['run_pair.py','run_ranges.py','run_trace.py','trace_source.py']:
        files['tools/'+name]=subprocess.check_output(['git','show',commit+':experiments/generic-sha-vector/'+name],cwd=ROOT)
    for name in ['fixtures.json','trace-fixtures.json']:
        files['bundle/'+name]=subprocess.check_output(['git','show',commit+':worker/promotion/validation/'+name],cwd=ROOT)
    files['host-full.sh']=subprocess.check_output(['git','show',commit+':experiments/generic-sha-vector/host-full.sh'],cwd=ROOT)
    files['ready.sh']=subprocess.check_output(['git','show',commit+':ops/aws-gpu-execution/ready.sh'],cwd=ROOT)
    result={}
    for name,raw in files.items():
        if name.startswith('tools/'):source='experiments/generic-sha-vector/'+name.split('/',1)[1]
        elif name.startswith('bundle/'):source='worker/promotion/validation/'+name.split('/',1)[1]
        elif name=='ready.sh':source='ops/aws-gpu-execution/ready.sh'
        else:source='experiments/generic-sha-vector/'+name
        result[name]={'sha256':hashlib.sha256(raw).hexdigest(),'url':'https://raw.githubusercontent.com/starknet-innovation/qsb-solver/'+commit+'/'+source}
    return result

def render(commit,url,image,stage,receipt_sha):
    if not re.fullmatch('[0-9a-f]{40}',commit):raise ValueError('commit required')
    if not url.startswith('https://') or any(c in url for c in '\r\n'):raise ValueError('HTTPS artifact URL required')
    if not re.fullmatch('ghcr.io/starknet-innovation/qsb-solver@sha256:[0-9a-f]{64}',image):raise ValueError('immutable runtime required')
    if stage not in ('ranges','trace') or not re.fullmatch('[0-9a-f]{64}',receipt_sha):raise ValueError('invalid gate binding')
    packed=base64.b64encode(zlib.compress(json.dumps(payload(commit)).encode())).decode()
    script="set -euo pipefail\nDEADLINE=__DEADLINE__\n"
    # Download immediately: the GitHub artifact URL is short-lived and scoped to public bytes.
    script+='curl --fail --location --max-time 120 --max-filesize 10000000 '+shlex.quote(url)+' -o /var/tmp/qsb-frozen-pair.zip\n'
    script+="python3 - <<'QSB_STAGE'\n"
    script+='import pathlib,hashlib,json,base64,zlib,zipfile,urllib.request\n'
    script+=f"archive=pathlib.Path('/var/tmp/qsb-frozen-pair.zip');assert hashlib.sha256(archive.read_bytes()).hexdigest()=={ZIP_SHA!r}\n"
    script+="root=pathlib.Path('/opt/qsb-a10g-gate');root.mkdir()\n"
    script+=f"files=json.loads(zlib.decompress(base64.b64decode({packed!r})))\n"
    script+="for name,item in files.items():\n raw=urllib.request.urlopen(item['url'],timeout=30).read(2000001);assert len(raw)<=2000000;assert hashlib.sha256(raw).hexdigest()==item['sha256'];p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)\n"
    script+=f"expected={BINARIES!r}\n"
    script+="with zipfile.ZipFile(archive) as z:\n assert len(z.namelist())==len(set(z.namelist()))\n for name in [*expected,'candidate-trace.diff','trace-receipt.json']:\n  info=z.getinfo(name);assert info.file_size<10000000;raw=z.read(name)\n  if name in expected:assert hashlib.sha256(raw).hexdigest()==expected[name]\n  p=root/'bundle'/name;p.write_bytes(raw)\n  if name in expected:p.chmod(0o755)\n"
    script+=f"assert hashlib.sha256((root/'bundle/trace-receipt.json').read_bytes()).hexdigest()=={receipt_sha!r}\n"
    script+="(root/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(root))+'\\n' for p in sorted(root.rglob('*')) if p.is_file()))\nQSB_STAGE\n"
    script+='bash /opt/qsb-a10g-gate/ready.sh "$DEADLINE"\n'
    script+='bash /opt/qsb-a10g-gate/host-full.sh '+shlex.quote(stage)+' '+shlex.quote(image)+' "$DEADLINE" '+shlex.quote(receipt_sha)+'\n'
    if len(script.encode())>60000:raise ValueError('SSM handoff too large')
    return script

if __name__=='__main__':
    commit,url_file,image,stage,receipt_sha,output=sys.argv[1:]
    script=render(commit,Path(url_file).read_text().strip(),image,stage,receipt_sha)
    with Path(output).open('x') as stream:stream.write(script)
