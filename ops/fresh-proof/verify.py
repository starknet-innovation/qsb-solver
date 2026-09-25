"""CPU-bound public evidence verification. Does not mutate authoritative coverage."""
import hashlib
import json
import re
from results import bind_result

COMMIT='43c77084648aa0f4cbcb1589abfcc792c9cc0d9d'


def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)


def verify(files, batch_raw, fixture, cpu, validate_batch, validate_binding, work_range, membership):
    summary=bind_result(files,batch_raw,validate_batch,validate_binding,work_range)
    if summary['requiresReconciliation']:
        raise ValueError('Resolve uncertain execution before CPU publication')
    batch=json.loads(batch_raw);request=batch['request'];state=json.loads(files['result.json'])
    if (fixture.get('network')!='regtest'
            or request.get('protocol')!='qsb-config-a-v1'
            or request.get('searchVersion')!='ranked-v2'
            or request.get('kernelCommit')!=COMMIT):
        raise ValueError('Wrong proof chain or worker contract')
    manifest_hash=hashlib.sha256(canonical(fixture['manifest']).encode()).hexdigest()
    if request.get('manifestHash')!=manifest_hash:
        raise ValueError('Wrong frozen manifest')
    export=dict(action='export',stage=request['stage'],publicStateJson=fixture['publicStateJson'],manifest=fixture['manifest'])
    if request['stage']!='pinning':
        if (type(request.get('sequence')) is not int or not 0x80000000<=request['sequence']<=0xffffffff
                or type(request.get('locktime')) is not int or not 500000000<=request['locktime']<1744600000):
            raise ValueError('Invalid subset pin context')
        export.update(sequence=request['sequence'],locktime=request['locktime'])
    params=cpu(export)
    if any(params.get(k)!=request.get(k) for k in ('parameterBase64','parameterSha256')):
        raise ValueError('GPU parameters differ from independent CPU export')
    checked=[];solution=None
    for row in state['results']:
        verdict=None
        hits=row['candidates']
        if hits:
            membership(request['stage'],hits,row['workRange'])
            verdict=cpu(dict(export,action='verify',candidates=hits))
            if verdict.get('valid') is True:
                solution=verdict
            elif verdict.get('valid') is not False or verdict.get('derOnly') is not True:
                raise ValueError('Unexpected CPU-rejected candidate; diagnose without retry')
        checked.append(dict(attempt=row['attempt'],workRange=row['workRange'],
                            cpuVerdict=verdict,wholeRangeEligible=not bool(hits)))
    # Even DER-only hits grant no whole-range credit. No nextAttempt is inferred
    # across a hit: its actual kernel coverage must be handled by the coordinator.
    return dict(batchId=batch['batchId'],requestId=fixture['requestId'],stage=request['stage'],
                manifestHash=manifest_hash,parameterSha256=params['parameterSha256'],
                resultSha256=hashlib.sha256(files['result.json'].encode()).hexdigest(),
                verifiedSolution=solution,rows=checked,grantsRangeCredit=False,
                requiresCandidateReconciliation=bool(checked and not checked[-1]['wholeRangeEligible']))


REFERENCE = {
    'bitcoin_tx.py':'c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c',
    'gpu_emulator.py':'449312593576ec4e59d8abe1b2f601d9c2d74d58c99dfe88924442a6cab4e896',
    'handler.py':'d08b7e530d2c140021bfeb645d229f8bb37e2c0f88100cdbe79b03432026a5c1',
    'qsb_pipeline.py':'05334c08fa012a77ccba2887e05d78f90a8b81c0e34b786931b423f7f11255d8',
    'secp256k1.py':'d2cebd1410b75cad606806cf02d7bee3e24724d5fcb7a53a07f598fcbc8afece',
    'verify_hit.py':'9f9e60952db15c054871403b60266d04c50d012e882bcd52a30f4bd3ba831fba',
}


class CpuReference:
    def __init__(self, source):
        from pathlib import Path
        self.source=Path(source)

    def __call__(self, event):
        from pathlib import Path
        import subprocess
        import sys
        import tempfile
        # Only a copied, hash-verified source set enters a new interpreter; no
        # pre-existing pyc, adjacent module or process-global reference state.
        with tempfile.TemporaryDirectory(prefix='qsb-public-cpu-') as directory:
            for name,expected in REFERENCE.items():
                path=self.source/name
                if path.is_symlink():raise ValueError('Reference symlink forbidden')
                raw=path.read_bytes()
                if hashlib.sha256(raw).hexdigest()!=expected:
                    raise ValueError('Frozen CPU reference changed')
                (Path(directory)/name).write_bytes(raw)
            script='import sys,json;sys.path.insert(0,sys.argv[1]);import handler;print(json.dumps(handler.handler(json.load(sys.stdin))))'
            result=subprocess.run([sys.executable,'-I','-c',script,directory],input=canonical(event),
                                  capture_output=True,text=True,timeout=120)
            if result.returncode:raise ValueError('Independent public CPU verification failed')
            return json.loads(result.stdout)


def main():
    import argparse
    import importlib.util
    from pathlib import Path
    from collect import save_new
    from results import decode_archive,unique_object
    parser=argparse.ArgumentParser()
    parser.add_argument('--collection',type=Path,required=True,help='Complete evidence directory')
    parser.add_argument('--fixture',type=Path,required=True)
    parser.add_argument('--fixture-sha256',required=True,help='Previously frozen public fixture hash')
    parser.add_argument('--reference',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    raw=args.fixture.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=args.fixture_sha256:raise ValueError('Fixture binding changed')
    fixture=json.loads(raw,object_pairs_hook=unique_object)
    receipt=json.loads((args.collection/'collection-receipt.json').read_text(),object_pairs_hook=unique_object)
    # Receipt keys cannot choose arbitrary filesystem paths.
    expected={'public-result.b64','batch.json','deadline.txt','gpu.txt','gate.log','exit-code.txt','result.json'}
    if set(receipt['files'])!=expected:raise ValueError('Invalid collection inventory')
    for name,expected_hash in receipt['files'].items():
        path=args.collection/name
        if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest()!=expected_hash:
            raise ValueError('Collected evidence changed')
    files=decode_archive((args.collection/'public-result.b64').read_bytes(),receipt['archive'])
    for name,value in files.items():
        if (args.collection/name).read_bytes()!=value.encode():raise ValueError('Extracted archive mismatch')
    root=Path(__file__).resolve().parents[2]
    def module(name,path):
        spec=importlib.util.spec_from_file_location(name,root/path)
        result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result
    runner=module('fresh_sm86','worker/promotion/validation/run_fresh_sm86.py')
    ranges=module('fresh_ranges','worker/search_ranges.py')
    membership=module('fresh_membership','worker/promotion/validation/candidate_range.py')
    result=verify(files,(args.collection/'batch.json').read_bytes(),fixture,CpuReference(args.reference),
                  runner.validate_batch,runner.validate_binding,ranges.work_range,membership.validate_candidates_in_range)
    result.update(fixtureSha256=args.fixture_sha256,referenceHashes=REFERENCE,
                  collectionReceiptSha256=hashlib.sha256((args.collection/'collection-receipt.json').read_bytes()).hexdigest())
    save_new(args.output,result)
    print(json.dumps(dict(batchId=result['batchId'],rows=len(result['rows']),
                         hasCpuVerifiedSolution=result['verifiedSolution'] is not None,grantsRangeCredit=False)))


if __name__=='__main__':main()
