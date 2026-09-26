"""Build the committed generic solver and derive new artifact identities; never enroll them."""
import hashlib,json,pathlib,shutil,subprocess,sys,os
ROOT=pathlib.Path('/src');SRC=ROOT/'research/optimized-subset';PKG=ROOT/'worker/optimized';OUT=pathlib.Path('/opt/qsb-validation')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):p.write_text(json.dumps(v,sort_keys=True,indent=2)+'\n')
def architecture_flags(flags, architecture):
 if architecture not in ('86','89'):raise ValueError('Unsupported CUDA architecture')
 if flags.count('-arch=sm_89') != 1 or any(f.startswith(('-gencode','--generate-code','--gpu-architecture','--gpu-code','-code=')) or (f.startswith('-arch') and f != '-arch=sm_89') for f in flags):
  raise ValueError('Unexpected locked architecture flags')
 return [f'-arch=sm_{architecture}' if f=='-arch=sm_89' else f for f in flags]

def main():
 lock=json.loads((PKG/'source-lock.json').read_text())
 architecture=os.environ.get('CUDA_ARCH','89');flags=architecture_flags(lock['flags'],architecture)
 actual={str(p.relative_to(SRC)) for p in (SRC/'subset').rglob('*') if p.is_file()}
 if actual!=set(lock['files']):raise ValueError('Unlisted or missing solver source')
 for n,want in lock['files'].items():
  p=SRC/n
  if p.is_symlink() or sha(p)!=want:raise ValueError('Solver source changed: '+n)
 if OUT.exists():raise ValueError('Refuse existing output')
 OUT.mkdir(parents=True);candidate=OUT/'candidate'
 shutil.copytree(PKG/'candidate',candidate);shutil.copytree(SRC/'subset',candidate/'source/subset')
 shutil.copyfile(SRC/'LICENSE',candidate/'source/LICENSE')
 for n in ['runtime.py','queue_handler.py']:shutil.copyfile(PKG/n,OUT/n)
 command=['nvcc',*flags,'-o',str(candidate/'subset'),str(SRC/'subset/subset.cu'),'-lcrypto','-lm']
 subprocess.run(command,check=True)
 save(candidate/'source-manifest.json',lock['files'])
 save(candidate/'release.json',{'id':'qsb-subset-public-build-v1','architecture':'sm_'+architecture,'baseKernelCommit':'1650caf53a32b0ea16aae9e490ebbf5a8686d632','protocol':'qsb-config-a-v1','searchVersion':'ranked-v2','purpose':'isolated-subset-validation-only','status':'HOLD','imageDigest':None,'files':{n:sha(candidate/n) for n in ['subset','candidate_handler.py','range_adapter.py','release_guard.py','search_ranges.py','source-manifest.json']}})
 names=['runtime.py','queue_handler.py','candidate/release.json']
 save(OUT/'runtime-binding.json',{'files':{n:sha(OUT/n) for n in names},'purpose':'isolated-compute-stdin-v1','status':'HOLD'})
 save(OUT/'build-receipt.json',{'sourceLockSha256':sha(PKG/'source-lock.json'),'flags':flags,'architecture':'sm_'+architecture,'compiler':subprocess.check_output(['nvcc','--version'],text=True),'packages':subprocess.check_output(['dpkg-query','-W','gcc','g++','libssl-dev'],text=True),'binarySha256':sha(candidate/'subset'),'solverReleaseSha256':sha(candidate/'release.json'),'runtimeHash':sha(OUT/'runtime-binding.json'),'status':'HOLD','historicalBinaryAttestation':False})
if __name__=='__main__':main()
