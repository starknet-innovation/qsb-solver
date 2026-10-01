"""Prepare fixed public table subprocess benchmark, never a solver."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
REUSE={'prepare_gpu.py':'d379101d3af10297bb31e82656ce61b64d753e571f44b07e11561f9f92540010','gpu-harness.cu.inc':'23bef5aafeccf6041feb2fd924c5308b313211cb469c24c0ab828b263c7fde32'}
EXPECTED_TABLE_SHA256='6c6af155b84552c23ee2fc17b29dfe31bad768b92ca43e3198efc7a0e097ad8f'
def sha(data):return hashlib.sha256(data).hexdigest()
def prepare(output,root=ROOT):
    reused=root/'experiments/host-ladder-batch'
    for name,want in REUSE.items():
        if sha((reused/name).read_bytes())!=want:raise ValueError('reused extraction changed: '+name)
    spec=importlib.util.spec_from_file_location('frozen_host_ladder_gpu_prepare',reused/'prepare_gpu.py')
    base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
    with tempfile.TemporaryDirectory() as directory:
        staged=Path(directory)/'staged';manifest=base.prepare(staged,root=root,here=reused)
        source=(staged/'table-gate.cu').read_bytes();old=(reused/'gpu-harness.cu.inc').read_bytes()
        if not source.endswith(old) or source.count(old)!=1:raise ValueError('isolated harness suffix mismatch')
        replacement=('#define EXPECTED_TABLE_SHA256 "'+EXPECTED_TABLE_SHA256+'"\n').encode()+(HERE/'harness.cu.inc').read_bytes()
        files={p.name:p.read_bytes() for p in staged.iterdir() if p.name!='manifest.json'}
        files['table-gate.cu']=source[:-len(old)]+replacement
    output.mkdir(parents=True,exist_ok=False)
    for name,data in files.items():(output/name).write_bytes(data)
    result={'schema':1,'scope':'fixed public synthetic table subprocess only','noSolverSearch':True,'repetitions':[1,4,16],'publicScalar':1,'expectedTableSha256':EXPECTED_TABLE_SHA256,'original_kernel_sha256':manifest['original_kernel_sha256'],'host_candidate_sha256':manifest['host_candidate_sha256'],'baseline_inputs':manifest['baseline_inputs'],'reused_sources':REUSE,'sources':{p:sha((HERE/p).read_bytes()) for p in ['prepare.py','harness.cu.inc']},'outputs':{p:sha(data) for p,data in files.items()},'status':'prepared-not-native-validated'}
    (output/'manifest.json').write_text(json.dumps(result,indent=2)+'\n');return result
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('output',type=Path);prepare(parser.parse_args().output)
