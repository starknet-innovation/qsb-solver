"""Compile an isolated baseline/candidate pair; never change production locks."""
import hashlib,json,pathlib,shutil,subprocess,difflib
from trace_source import instrument
root=pathlib.Path('/src');src=root/'research/optimized-subset'
lock=json.loads((root/'worker/optimized/source-lock.json').read_text())
actual={str(p.relative_to(src)) for p in (src/'subset').rglob('*') if p.is_file()}
if actual!=set(lock['files']):raise ValueError('Source inventory mismatch')
for name,want in lock['files'].items():
 p=src/name
 if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=want:raise ValueError('Source mismatch: '+name)
flags=[x.replace('-arch=sm_89','-arch=sm_86') for x in lock['flags']]
out=pathlib.Path('/results');out.mkdir(exist_ok=False)
records={}
for variant in ['baseline','candidate']:
 work=pathlib.Path('/tmp')/variant;shutil.copytree(src,work)
 if variant=='candidate':subprocess.run(['patch','--batch','-p1','-i',str(root/'experiments/generic-sha-vector/generic-tail-vector.patch')],cwd=work,check=True)
 command=['nvcc',*flags,'-Xptxas=-v','-o',str(out/variant),str(work/'subset/subset.cu'),'-lcrypto','-lm']
 with (out/(variant+'.log')).open('w') as f:subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=480)
 records[variant]={'binarySha256':hashlib.sha256((out/variant).read_bytes()).hexdigest(),'treeSha256':hashlib.sha256((work/'subset/tests/gpu_epochs/tree.cu').read_bytes()).hexdigest()}
(out/'build.json').write_text(json.dumps({'flags':flags,'binaries':records,'compiler':subprocess.check_output(['nvcc','--version'],text=True),'packages':subprocess.check_output(['dpkg-query','-W','gcc','g++','libssl-dev'],text=True),'gpuExecuted':False,'status':'HOLD'},indent=2)+'\n')

# Diagnostic derivative only: preserve the exact pair above for execution/timing.
tree=pathlib.Path('/tmp/candidate/subset/tests/gpu_epochs/tree.cu')
original=tree.read_text();changed=instrument(original)
trace_root=pathlib.Path('/tmp/candidate-trace');shutil.copytree(pathlib.Path('/tmp/candidate'),trace_root)
(trace_root/'subset/tests/gpu_epochs/tree.cu').write_text(changed)
patch=out/'candidate-trace.diff'
patch.write_text(''.join(difflib.unified_diff(original.splitlines(True),changed.splitlines(True),fromfile='candidate/tree.cu',tofile='trace/tree.cu')))
command=['nvcc',*flags,'-Xptxas=-v','-o',str(out/'candidate-trace'),str(trace_root/'subset/subset.cu'),'-lcrypto','-lm']
with (out/'candidate-trace.log').open('w') as f:subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=480)
(out/'trace-receipt.json').write_text(json.dumps(dict(
    unmodifiedBinarySha256=records['candidate']['binarySha256'],
    unmodifiedTreeSha256=records['candidate']['treeSha256'],
    diagnosticTreeSha256=hashlib.sha256(changed.encode()).hexdigest(), flags=flags,
    files={name:hashlib.sha256((out/name).read_bytes()).hexdigest() for name in ['candidate-trace','candidate-trace.diff']},
    status='UNEXECUTED',cpuVerified=False,
    scope='Diagnostic derivative; does not attest execution of the unmodified binary'),indent=2)+'\n')
