"""Build public batches from the frozen fixture and authoritative proof progress.

No provider writes, no funding/signing and no GPU execution. Planning is not admission.
"""
import argparse
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import uuid
from budget import Budget,canonical
from collect import load,save_new
from control import ROOT,SOURCE,IMAGE,Guard,owner_lock,source_identity
from journal import Journal
from verify import CpuReference


def dependencies():
    def module(name,path):
        spec=importlib.util.spec_from_file_location(name,ROOT/path)
        result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result
    return (module('proof_runner','worker/promotion/validation/run_fresh_sm86.py'),
            module('proof_ranges','worker/search_ranges.py'))


def frozen_fixture(path, expected, campaign, public_request):
    raw=Path(path).read_bytes()
    if hashlib.sha256(raw).hexdigest()!=expected:raise ValueError('frozen fixture hash mismatch')
    from results import unique_object
    fixture=json.loads(raw,object_pairs_hook=unique_object)
    request_raw=Path(public_request).read_bytes()
    if hashlib.sha256(request_raw).hexdigest()!=campaign['requestHash']:
        raise ValueError('public request byte hash mismatch')
    request=json.loads(request_raw,object_pairs_hook=unique_object)
    canonical_hash=hashlib.sha256(canonical(request).encode()).hexdigest()
    if (fixture.get('network')!='regtest' or fixture.get('requestId')!=campaign['campaignId']
            or request.get('id')!=campaign['campaignId'] or fixture.get('requestSha256')!=canonical_hash):
        raise ValueError('fixture chain/request binding mismatch')
    return fixture


def build(snapshot,fixture,cpu,max_attempts,work_range):
    stage,attempt=snapshot['stage'],snapshot['nextAttempt'];binding=snapshot['binding']
    if (stage not in ('pinning','round1','round2') or type(attempt) is not int or attempt<0
            or type(max_attempts) is not int or not 1<=max_attempts<=64):
        raise ValueError('invalid active progress or batch bound')
    if (fixture.get('network')!='regtest' or fixture.get('requestId')!=binding['requestId']
            or hashlib.sha256(canonical(fixture['manifest']).encode()).hexdigest()!=binding['manifestHash']):
        raise ValueError('fixture differs from durable proof binding')
    # Reject exhaustion before any parameter export or resource reservation.
    work_range(stage,attempt)
    count=1
    for offset in range(1,max_attempts):
        try:work_range(stage,attempt+offset)
        except ValueError as error:
            if str(error)!='Search range exhausted':raise
            break
        count+=1
    event=dict(action='export',stage=stage,publicStateJson=fixture['publicStateJson'],manifest=fixture['manifest'])
    context={}
    if stage!='pinning':
        pin=snapshot['solutions'].get('pinning',{})
        if (pin.get('valid') is not True or type(pin.get('sequence')) is not int
                or not 0x80000000<=pin['sequence']<=0xffffffff or type(pin.get('locktime')) is not int
                or not 500000000<=pin['locktime']<1744600000):raise ValueError('verified pin required')
        context={k:pin[k] for k in ('sequence','locktime')};event.update(context)
    params=cpu(event)
    raw=base64.b64decode(params['parameterBase64'],validate=True)
    if not raw or len(raw)>100_000 or hashlib.sha256(raw).hexdigest()!=params['parameterSha256']:
        raise ValueError('invalid CPU parameter export')
    request=dict(protocol='qsb-config-a-v1',searchVersion='ranked-v2',kernelCommit=SOURCE,
                 stage=stage,attempt=attempt,manifestHash=binding['manifestHash'],**context,
                 parameterBase64=params['parameterBase64'],parameterSha256=params['parameterSha256'])
    return dict(batchId=str(uuid.uuid4()),request=request,maxAttempts=count)


def validate_planned(batch_raw,snapshot,fixture,cpu,work_range):
    from results import unique_object
    batch=json.loads(batch_raw,object_pairs_hook=unique_object)
    expected=build(snapshot,fixture,cpu,batch['maxAttempts'],work_range)
    expected['batchId']=batch['batchId']
    if batch!=expected:raise ValueError('stale or modified planned batch')
    return batch


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('mode',choices=['init','plan','register'])
    for name in ('ledger','campaign','fixture','public-request'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--fixture-sha256',help='Previously frozen digest, required for init')
    parser.add_argument('--reference',type=Path)
    parser.add_argument('--batch',type=Path)
    parser.add_argument('--execution',type=Path)
    parser.add_argument('--max-attempts',type=int,default=8)
    args=parser.parse_args();campaign=load(args.campaign)
    if campaign.get('candidateSource')!=SOURCE or campaign.get('imageDigest')!=IMAGE:raise ValueError('wrong frozen candidate')
    budget=Budget(args.ledger,campaign);journal=Journal(budget)
    with owner_lock(budget.path):
        source_identity()
        if args.mode=='init':
            if not args.fixture_sha256:raise ValueError('previously frozen fixture digest required')
            fixture=frozen_fixture(args.fixture,args.fixture_sha256,campaign,args.public_request)
            manifest_hash=hashlib.sha256(canonical(fixture['manifest']).encode()).hexdigest()
            journal.initialize(args.fixture_sha256,manifest_hash,fixture['requestId'])
            result=dict(status='initialized',requestId=fixture['requestId'])
        else:
            if args.reference is None or args.batch is None:raise ValueError('reference and public batch path required')
            snapshot=journal.snapshot();fixture=frozen_fixture(args.fixture,snapshot['binding']['fixtureSha256'],campaign,args.public_request)
            runner,ranges=dependencies()
            if args.mode=='plan':
                batch=build(snapshot,fixture,CpuReference(args.reference),args.max_attempts,ranges.work_range)
                runner.validate_batch(batch);save_new(args.batch,batch)
                result=dict(status='planned-not-admitted',batchId=batch['batchId'],stage=batch['request']['stage'],attempt=batch['request']['attempt'])
            else:
                if args.execution is None:raise ValueError('reserved execution path required')
                state=load(args.execution)
                Guard(budget,state['token'],args.execution,campaign).check(args.execution,state,'register')
                batch_raw=args.batch.read_bytes()
                # Compare precisely the bytes subsequently persisted by register.
                batch=validate_planned(batch_raw,snapshot,fixture,CpuReference(args.reference),ranges.work_range)
                journal.register(state['token'],batch_raw,runner.validate_batch)
                result=dict(status='registered-before-launch',batchId=batch['batchId'])
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':main()
