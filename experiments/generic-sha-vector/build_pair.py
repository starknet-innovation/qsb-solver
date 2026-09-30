"""Compile an isolated baseline/candidate pair; never change production locks."""
import hashlib,json,pathlib,shutil,subprocess
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
