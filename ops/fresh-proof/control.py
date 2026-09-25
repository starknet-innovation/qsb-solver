"""Budget-mandatory wrapper for the committed one-shot AWS controller.

No solver execution or automatic retries. Public campaign and state files only.
"""
import argparse
from contextlib import contextmanager
from decimal import Decimal
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
import uuid
from budget import Budget, canonical

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('aws_execution', ROOT/'ops/aws-gpu-execution/control.py')
AWS = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(AWS)
ALLOWANCE = 2_000_000  # entire allowance consumed; no optimistic billing refunds
SOURCE = '43c77084648aa0f4cbcb1589abfcc792c9cc0d9d'
IMAGE = 'e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d'


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def pricing(service, filters):
    return json.loads(subprocess.check_output(['aws','--profile','snf','--region','us-east-1',
        'pricing','get-products','--service-code',service,'--filters',canonical([
        dict(Type='TERM_MATCH',Field=k,Value=v) for k,v in filters.items()]),'--output','json'], text=True, timeout=60))


def price_quote(fetch=pricing):
    specs = [
        ('compute', 'AmazonEC2', dict(regionCode='eu-west-1',instanceType='g5.xlarge',
          operatingSystem='Linux',tenancy='Shared',preInstalledSw='NA',capacitystatus='Used'), 'Hrs', Decimal('1.123')),
        ('storage', 'AmazonEC2', dict(regionCode='eu-west-1',usagetype='EU-EBS:VolumeUsage.gp3'), 'GB-Mo', Decimal('0.10')),
        ('ipv4', 'AmazonVPC', dict(regionCode='eu-west-1',usagetype='EU-PublicIPv4:InUseAddress'), 'Hrs', Decimal('0.005'))]
    receipts = {}; rates = {}
    for label, service, filters, unit, ceiling in specs:
        response = fetch(service, filters); receipts[label] = response
        values = []
        for raw in response['PriceList']:
            product = json.loads(raw)
            if any(product['product']['attributes'].get(k) != v for k,v in filters.items()):
                raise ValueError('price response scope mismatch')
            for term in product['terms']['OnDemand'].values():
                for dimension in term['priceDimensions'].values():
                    if dimension['unit'] != unit or dimension['beginRange'] != '0' or dimension['endRange'] != 'Inf':
                        raise ValueError('unexpected tiered price')
                    values.append(Decimal(dimension['pricePerUnit']['USD']))
        if len(values) != 1 or not values[0].is_finite() or not 0 < values[0] <= ceiling:
            raise ValueError('missing, ambiguous or above-ceiling price')
        rates[label] = str(values[0])
    # One full hour of EC2/IP and 80GB gp3, despite a 25min guest deadline,
    # plus USD0.50 ancillary/shutdown allowance stays below the USD2 debit.
    bound = Decimal(rates['compute']) + Decimal(rates['ipv4']) + 80*Decimal(rates['storage'])/672 + Decimal('0.50')
    if bound*1_000_000 > ALLOWANCE:
        raise ValueError('session allowance insufficient')
    return dict(observedAt=int(time.time()), rates=rates, receipts=receipts,
                allowanceMicroUsd=ALLOWANCE, infrastructureHoursReserved=1,
                deadlineSeconds=1500, rootVolumeGiB=80)


@contextmanager
def owner_lock(ledger):
    path = Path(str(ledger)+'.controller.lock')
    if path.is_symlink(): raise ValueError('lock symlink forbidden')
    with path.open('a+') as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        try: yield
        finally: fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


class Guard:
    def __init__(self, ledger, token, state, campaign):
        self.ledger=ledger; self.token=token; self.state=state.resolve()
        self.binding=dict(ledger=str(ledger.path),campaignSha256=digest(campaign),intent=token)

    def check(self, path, state, mode):
        record=self.ledger.get(self.token)
        if (path.resolve()!=self.state or state.get('token')!=self.token or
            state.get('proofBudget')!=self.binding or record['state']=='settled' or
            record['request']['statePath']!=str(self.state)):
            raise ValueError('budget/state binding mismatch')
        expected_name='qsb-bench-'+self.token[:8]
        if state.get('name')!=expected_name:
            raise ValueError('infrastructure name must match reserved token')
        if any(state.get(k)!=v for k,v in record['scope'].items()):
            raise ValueError('frozen infrastructure binding changed')
        if mode in ('arm','launch') and not {'name','controllerCommit','securityGroup','functionArn'} <= set(record['scope']):
            raise ValueError('preparation receipt missing; reconcile before further paid work')
        if record['amount'] != ALLOWANCE:
            raise ValueError('full session not reserved')
        if mode!='cleanup' and record['request']['controllerCommit']!=state['controllerCommit']:
            raise ValueError('controller changed')


def source_identity():
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT):
        raise ValueError('dirty controller source; no reservation created')
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    remote=subprocess.check_output(['git','rev-parse','@{upstream}'],cwd=ROOT,text=True).strip()
    if commit!=remote:raise ValueError('controller source not pushed')
    return commit


def execute(mode, state, ledger, campaign, fetch_prices=price_quote, controller=AWS):
    state=Path(state).resolve()
    if campaign.get('candidateSource')!=SOURCE or campaign.get('imageDigest')!=IMAGE:
        raise ValueError('wrong frozen candidate')
    with owner_lock(ledger.path):
        commit=source_identity()
        if mode=='prepare':
            if state.exists(): raise ValueError('existing state; reconcile')
            quote=fetch_prices()
            if quote['allowanceMicroUsd']!=ALLOWANCE or not 0<=time.time()-quote['observedAt']<=300:
                raise ValueError('invalid or stale quote')
            token=str(uuid.uuid4())
            request=dict(statePath=str(state), controllerCommit=commit, quote=quote,
                         region='eu-west-1',instanceType='g5.xlarge',maxCount=1)
            ledger.reserve(token,request,ALLOWANCE)
        else:
            s=json.loads(state.read_text());token=s['token']
        guard=Guard(ledger,token,state,campaign)
        if mode!='prepare':guard.check(state,s,mode)
        if mode in ('arm','launch'):
            # Refresh every paid transition; never use an old cheap quote.
            quote=fetch_prices()
            if quote['allowanceMicroUsd']!=ALLOWANCE or not 0<=time.time()-quote['observedAt']<=300:
                raise ValueError('stale transition quote')
            with state.with_name('price-'+mode+'.json').open('x') as f:json.dump(quote,f)
        if mode!='cleanup':ledger.claim_operation(token,mode)
        previous=sys.argv
        try:
            sys.argv=[str(ROOT/'ops/aws-gpu-execution/control.py'),mode,'--state',str(state)]
            controller.main(proof=guard)
        except RuntimeError as error:
            explicit='An error occurred (InsufficientInstanceCapacity) when calling the RunInstances operation'
            if mode=='launch' and explicit in str(error) and json.loads(state.read_text()).get('phase')=='launch-intent':
                ledger.record_capacity_rejection(token,dict(code='InsufficientInstanceCapacity',clientToken=token,
                    controllerErrorSha256=hashlib.sha256(str(error).encode()).hexdigest()))
            raise
        finally:sys.argv=previous
        s=json.loads(state.read_text())
        ledger.bind_scope(token,{k:s[k] for k in ['name','controllerCommit','securityGroup','functionArn','deadline','schedule'] if k in s})
        if mode=='launch':
            actual=controller.aws('ec2','describe-instances',InstanceIds=[s['instanceId']])
            instance=actual['Reservations'][0]['Instances'][0]
            if instance['ClientToken']!=token:raise ValueError('provider token mismatch')
            volumes=[v['Ebs']['VolumeId'] for v in instance['BlockDeviceMappings']]
            s['volumeIds']=volumes;controller.save(state,s)
            ledger.attach(token,ledger.get(token)['request'],dict(instanceId=s['instanceId'],volumeIds=volumes,clientToken=token))
        return ledger.snapshot()


def reconcile(state, ledger, campaign, controller=AWS):
    state=Path(state).resolve()
    with owner_lock(ledger.path):
        s=json.loads(state.read_text());token=s['token']
        Guard(ledger,token,state,campaign).check(state,s,'cleanup')
        if controller.aws('sts','get-caller-identity')['Account']!='905846953990':
            raise ValueError('wrong cleanup account')
        observations={}
        lifetime=None
        for key in ['client-token','tag:QsbBenchmarkToken']:
            observations[key]=[i for r in controller.aws('ec2','describe-instances',Filters=[dict(Name=key,Values=[token])])['Reservations'] for i in r['Instances']]
        ids=[{i['InstanceId'] for i in observations[key]} for key in observations]
        if ids[0]!=ids[1] or len(ids[0])>1:
            raise ValueError('provider identity discrepancy; cleanup-only reconciliation required')
        record=ledger.get(token)
        if ids[0]:
            i=observations['client-token'][0]
            if i.get('ClientToken')!=token:raise ValueError('wrong provider token')
            launched=datetime.fromisoformat(i['LaunchTime'].replace('Z','+00:00'))
            if launched.tzinfo is None:raise ValueError('missing timezone on launch time')
            lifetime=datetime.now(timezone.utc).timestamp()-launched.timestamp()
            if not 0<=lifetime<=3600:
                raise ValueError('observed lifetime exceeds reserved hour; do not unlock budget')
            if record['resource'] is None:
                volumes=[v['Ebs']['VolumeId'] for v in i['BlockDeviceMappings']]
                ledger.attach(token,record['request'],dict(instanceId=i['InstanceId'],volumeIds=volumes,clientToken=token))
                record=ledger.get(token)
            if i['InstanceId']!=record['resource']['instanceId'] or i['State']['Name']!='terminated':
                raise ValueError('instance not terminal; terminate before settlement')
        elif record['resource'] is not None:
            raise ValueError('attached instance disappeared; absence is not terminal evidence')
        elif not record['evidence'] or record['evidence'].get('code')!='InsufficientInstanceCapacity':
            raise ValueError('unknown outcome remains reserved')
        volumes=record['resource']['volumeIds'] if record['resource'] else []
        remaining=[]
        if volumes:remaining=controller.aws('ec2','describe-volumes',Filters=[dict(Name='volume-id',Values=volumes)])['Volumes']
        if ids[0]:remaining+=controller.aws('ec2','describe-volumes',Filters=[dict(Name='attachment.instance-id',Values=sorted(ids[0]))])['Volumes']
        name='qsb-bench-'+token[:8]
        groups=controller.aws('ec2','describe-security-groups',Filters=[dict(Name='group-name',Values=[name])])['SecurityGroups']
        schedules=controller.aws('scheduler','list-schedules',NamePrefix=name)['Schedules']
        functions=[x for x in controller.aws('lambda','list-functions')['Functions'] if x['FunctionName']==name]
        roles=[x for x in controller.aws('iam','list-roles')['Roles'] if x['RoleName'].startswith(name)]
        profiles=[x for x in controller.aws('iam','list-instance-profiles')['InstanceProfiles'] if x['InstanceProfileName']==name]
        counts=dict(volumesRemaining=len(remaining),securityGroupsRemaining=len(groups),schedulesRemaining=len(schedules),
                    functionsRemaining=len(functions),rolesRemaining=len(roles),instanceProfilesRemaining=len(profiles))
        if any(counts.values()):raise ValueError('temporary resources remain')
        receipt=dict(observedAt=int(time.time()),clientToken=token,instancesByToken=len(ids[0]),instancesByTag=len(ids[1]),
                     instanceId=next(iter(ids[0]),None),volumeIds=volumes,lifetimeSeconds=lifetime,**counts)
        with state.with_name('cleanup-'+str(uuid.uuid4())+'.json').open('x') as f:json.dump(receipt,f,indent=2)
        if record['resource']:
            ledger.settle(token,dict(instanceId=record['resource']['instanceId'],instanceState='terminated',volumeIds=volumes,
                                    receiptSha256=digest(receipt),**counts))
        else:
            ledger.settle_rejected(token,dict(clientToken=token,instancesByToken=0,instancesByTag=0,
                                             receiptSha256=digest(receipt),**counts))
        return ledger.snapshot()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['init','prepare','arm','launch','cleanup','reconcile'])
    p.add_argument('--ledger',type=Path,required=True)
    p.add_argument('--campaign',type=Path,required=True)
    p.add_argument('--state',type=Path)
    a=p.parse_args();campaign=json.loads(a.campaign.read_text())
    if a.mode=='init':print(canonical(Budget.create(a.ledger,campaign).snapshot()));return
    if a.state is None:p.error('--state required')
    ledger=Budget(a.ledger,campaign)
    result=reconcile(a.state,ledger,campaign) if a.mode=='reconcile' else execute(a.mode,a.state,ledger,campaign)
    print(canonical(result))


if __name__=='__main__':main()
