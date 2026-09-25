"""Bounded sm86 component audits; no fresh search, signing or durable coverage."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from run_a10g import validate_binding, PIN, SUB


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('bundle',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('manifest_sha')
    args=parser.parse_args()
    root=args.bundle.resolve()
    manifest_path=root/'audit-manifest.json'
    if sha(manifest_path)!=args.manifest_sha: raise ValueError('unexpected audit manifest')
    manifest=json.loads(manifest_path.read_text())
    actual={str(p.relative_to(root)):sha(p) for d in ['edge','curve','pinning'] for p in (root/d).rglob('*') if p.is_file()}
    if actual!=manifest['artifacts']: raise ValueError('audit artifact inventory/hash mismatch')
    for key in actual:
        if (root/key).is_symlink(): raise ValueError('symlink audit input')
    sys.path.insert(0,'/opt/qsb');import handler
    binding=handler.release_binding();validate_binding(binding)
    for kind in ['edge','curve']:
        receipt=json.loads((root/kind/'receipt.json').read_text())
        if receipt['architecture']!='sm_86' or receipt['unmodifiedBinarySha256']!=SUB or receipt['sourceLockSha256']!=binding['subsetSourceLockSha256']:
            raise ValueError('wrong subset diagnostic lineage')
    pin=json.loads((root/'pinning/receipt.json').read_text())
    if pin['architecture']!='sm_86' or pin['files']['pinning']!=PIN: raise ValueError('wrong pinning diagnostic lineage')
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines())!=1 or 'A10G' not in gpu: raise ValueError('exactly one A10G required')
    with args.output.open('x') as f: json.dump({'status':'running','binding':binding},f)
    deadline=time.monotonic()+600
    results=dict(status='running',binding=binding,gpu=gpu,phases={},freshWithdrawal=False)
    with tempfile.TemporaryDirectory() as tmp:
        work=Path(tmp)
        for d in ['edge','curve','pinning']: shutil.copytree(root/d,work/d)
        params=work/'pin.bin'
        fixtures=json.loads((work/'edge/fixtures.json').read_text())
        params.write_bytes(base64.b64decode(fixtures['pinning']['parameterBase64'],validate=True))
        jobs=[('pinning-host',[sys.executable,str(root/'run_pinning_audit.py'),'--artifacts',str(work/'pinning'),'--params',str(params),'--output',str(work/'pinning-host.json')]),
              ('curve',[sys.executable,str(root/'run_curve.py'),str(work/'curve'),sha(work/'curve/receipt.json')])]
        for phase,module in [('edge','run_edge_audit'),('memory','run_memory_audit')]:
            # Existing sm89 harnesses are preserved. Bind their exact-binary guards
            # to the independently checked sm86 target, never to caller hashes.
            code='import sys;sys.path.insert(0,sys.argv.pop(1));import '+module+' as m;from run_a10g import PIN,SUB;m.PIN=PIN;m.SUB=SUB;m.main()'
            jobs.append((phase,[sys.executable,'-c',code,str(root),str(work/'edge'),str(work/(phase+'.json'))]))
        for phase,command in jobs:
            remaining=deadline-time.monotonic()
            if remaining<=0: raise TimeoutError('audit batch deadline')
            proc=subprocess.run(command,text=True,capture_output=True,timeout=remaining)
            record=dict(exit=proc.returncode,stdout=proc.stdout,stderr=proc.stderr)
            if (work/(phase+'.json')).exists(): record['result']=json.loads((work/(phase+'.json')).read_text())
            results['phases'][phase]=record
            args.output.write_text(json.dumps(results,indent=2)+'\n')
            print('PHASE',phase,'EXIT',proc.returncode,flush=True)
            if proc.returncode: raise RuntimeError('audit phase failed: '+phase)
    results['status']='native-components-completed-awaiting-cpu-review'
    args.output.write_text(json.dumps(results,indent=2)+'\n')
    print('QSB_AUDIT_RESULT_SHA256='+sha(args.output),flush=True)


if __name__=='__main__':main()
