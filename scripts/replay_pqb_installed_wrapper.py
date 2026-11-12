"""Inside-image wrapper replay of retained grinder transcripts. No real grinder/GPU runs."""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch


def main():
    sys.path.insert(0,'/opt/qsb-pqb')
    import pqb_handler as worker
    raw=Path(sys.argv[1]).read_bytes();expected_hash=sys.argv[2];expected_source=sys.argv[3]
    if hashlib.sha256(raw).hexdigest()!=expected_hash:raise ValueError('Retained transcript archive differs')
    files=json.loads(gzip.decompress(raw));binding=worker.release_binding()
    if binding['solverCommit']!=expected_source:raise ValueError('Actual installed source differs')
    rows=[]
    for stage in ('pinning','round0','round1'):
        prefix='unit/'+stage+'/'
        request=json.loads(files[prefix+'request.json'])
        request['input']['kernelCommit']=expected_source  # synthetic compatibility vector, explicitly not a native result
        old=json.loads(files[prefix+'worker-result.json'])
        log,hits=files[prefix+'work/compute.log'],files[prefix+'work/hits.txt']
        calls=[]
        def simulated(command,*,cwd,stdout,**kwargs):
            calls.append(command)
            if Path(cwd,'P.txt').read_text()!=files[prefix+'work/P.txt']:
                raise ValueError('Installed wrapper changed the public problem')
            Path(cwd,'hits.txt').write_text(hits);stdout.write(log)
            return SimpleNamespace(wait=lambda timeout:0,returncode=0)
        with patch.object(worker.subprocess,'Popen',simulated):response=worker.handler(request)
        if len(calls)!=1 or calls[0][0]!='/opt/qsb-pqb/grind':raise ValueError('Unexpected installed invocation')
        expected=copy.deepcopy(old);expected['kernelCommit']=expected_source
        for value in (expected,response):value.pop('elapsedSeconds',None)
        if response!=expected:raise ValueError('Installed wrapper changed response semantics')
        fixture='pin' if stage=='pinning' else stage
        rows.append(dict(stage=stage,response=response,problem=files[prefix+'work/P.txt'],
            packet=Path('/public-fixtures',fixture+'.packet.json').read_text(),command=calls[0]))
    print(json.dumps(dict(format='qsb-pqb-installed-wrapper-replay-v1',status='passed',
        assessedSourceCommit=expected_source,binding=binding,originalNativeArchiveSha256=expected_hash,
        originalNativeImage=json.loads(files['runtime-identity-check.json'])['imageDigest'],
        simulatedGrinder=True,freshNativeExecution=False,computeSubmitted=False,rows=rows,
        limits=['Actual installed Python wrapper; retained validated transcript is mocked at Popen',
                'No new GPU result, latency, provider job, range credit or complete solve']),indent=2))


if __name__=='__main__':main()
