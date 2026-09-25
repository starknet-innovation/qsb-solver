"""Bind settled host execution and collected bytes to independent CPU publication.

SSM is provider execution evidence, not hardware attestation. The host command
must have been reviewed and frozen before submission; this module never sends it.
"""
import hashlib
import json
from pathlib import Path
from collect import invocation, load, aws_cli
from verify import verify_collection


class EvidenceVerifier:
    def __init__(self, collection, fixture, fixture_sha256, reference, aws):
        self.collection=Path(collection)
        self.fixture=Path(fixture)
        self.fixture_sha256=fixture_sha256
        self.reference=Path(reference)
        self.aws=aws

    def __call__(self, batch_raw, resource, command_id, command_text):
        instance=resource['instanceId']
        expected=dict(instanceId=instance,commandId=command_id,
                      batchSha256=hashlib.sha256(batch_raw).hexdigest())
        if load(self.collection/'context.json')!=expected:
            raise ValueError('collection/provider context mismatch')
        evidence=self.collection/'evidence'
        if (evidence/'batch.json').read_bytes()!=batch_raw:
            raise ValueError('collected batch differs from durable intent')
        commands=self.aws(['ssm','list-commands','--command-id',command_id]).get('Commands',[])
        if len(commands)!=1:raise ValueError('missing unique provider command')
        command=commands[0]
        if (command.get('CommandId')!=command_id or command.get('InstanceIds')!=[instance]
                or command.get('DocumentName')!='AWS-RunShellScript'
                or command.get('Parameters',{}).get('commands')!=[command_text]
                or command.get('Status')!='Success'):
            raise ValueError('provider command differs from frozen submission or failed')
        result=invocation(self.aws,command_id,instance)
        if result.get('Status')!='Success' or result.get('ResponseCode')!=0:
            raise ValueError('provider invocation did not succeed')
        lines=[line.split('=',1)[1] for line in result.get('StandardOutputContent','').splitlines()
               if line.startswith('QSB_PUBLIC_RESULT_META=')]
        if len(lines)!=1:raise ValueError('missing unique provider result receipt')
        from results import unique_object
        meta=json.loads(lines[0],object_pairs_hook=unique_object)
        receipt=load(evidence/'collection-receipt.json')
        if meta!=load(self.collection/'metadata.json') or meta!=receipt['archive']:
            raise ValueError('provider archive receipt changed')
        checked=verify_collection(evidence,self.fixture,self.fixture_sha256,self.reference)
        checked['providerBinding']=expected
        checked['hostCommandSha256']=hashlib.sha256(command_text.encode()).hexdigest()
        return checked


def main():
    import argparse
    import sys
    from budget import Budget
    from journal import Journal
    from control import owner_lock,SOURCE,IMAGE
    parser=argparse.ArgumentParser()
    for name in ('ledger','campaign','collection','fixture','reference'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--token',required=True)
    parser.add_argument('--command',required=True)
    args=parser.parse_args()
    campaign=load(args.campaign)
    if campaign.get('candidateSource')!=SOURCE or campaign.get('imageDigest')!=IMAGE:
        raise ValueError('wrong frozen campaign candidate')
    if aws_cli(['sts','get-caller-identity'])['Account']!='905846953990':
        raise ValueError('wrong AWS account')
    budget=Budget(args.ledger,campaign)
    sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'worker'))
    from search_ranges import work_range
    with owner_lock(budget.path):
        journal=Journal(budget)
        fixture_hash=journal.snapshot()['binding']['fixtureSha256']
        verifier=EvidenceVerifier(args.collection,args.fixture,fixture_hash,args.reference,aws_cli)
        result=journal.publish(args.token,args.command,verifier,work_range)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':main()
