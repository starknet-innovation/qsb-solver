"""Build a public gate archive from committed sources and verified release binaries."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT=Path(__file__).resolve().parents[1]
BINARIES={'subset':'672cf6689fd6e0c71d992ab2a6df2687ac9b2b0d5c7de42d63db6b51b69c6b5d',
          'pinning':'f97d6a95a57841a619f1b842e3007320af1c0ff17f60366bb1b8b80912fe40e0'}
FILES=['benchmark.py','run_a10g.py','run_a10g_performance.py','run_a10g_pinning_performance.py',
       'fixtures.json','pinning-fixtures.json']

def prepare(commit,baseline,output):
    actual=subprocess.check_output(['git','rev-parse',commit+'^{commit}'],cwd=ROOT,text=True).strip()
    if commit!=actual:raise ValueError('Full immutable source commit required')
    files={name:subprocess.check_output(['git','show',commit+':worker/promotion/validation/'+name],cwd=ROOT) for name in FILES}
    files['host-a10g-performance.sh']=subprocess.check_output(['git','show',commit+':ops/aws-gpu-execution/host-a10g-performance.sh'],cwd=ROOT)
    for name,digest in BINARIES.items():
        raw=(Path(baseline)/name).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Released baseline hash mismatch: '+name)
        files['baseline/'+name]=raw
    files['source-commit.txt']=(commit+'\n').encode()
    hashes={name:hashlib.sha256(raw).hexdigest() for name,raw in files.items()}
    files['SHA256SUMS']=''.join(f'{hashes[n]}  {n}\n' for n in sorted(hashes)).encode()
    output=Path(output)
    with output.open('xb') as stream:
        with tarfile.open(fileobj=stream,mode='w:gz') as archive:
            for name in sorted(files):
                member=tarfile.TarInfo(name);member.size=len(files[name]);member.mtime=0
                member.mode=0o755 if name.startswith('baseline/') or name.endswith('.sh') else 0o644
                archive.addfile(member,io.BytesIO(files[name]))
    return dict(sourceCommit=commit,sha256=hashlib.sha256(output.read_bytes()).hexdigest(),files=hashes,
                stages=['pinning','subset'],executionPerformed=False)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--commit',required=True);p.add_argument('--baseline',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();print(json.dumps(prepare(a.commit,a.baseline,a.output),indent=2))
