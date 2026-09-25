"""Exactly one public host command per reserved/registered proof session.

No infrastructure allocation or automatic retry. An uncertain send stays claimed.
"""
import base64
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import time
from collect import aws_cli,load,save_new
from control import ROOT,Guard,owner_lock,source_identity,SOURCE,IMAGE
from journal import Journal
from budget import Budget

PUBLIC_SCRIPTS={
    'run_fresh_sm86.py':'worker/promotion/validation/run_fresh_sm86.py',
    'host-a10g-fresh.sh':'ops/aws-gpu-execution/host-a10g-fresh.sh',
}


def build_command(batch_raw, scripts, ready, deadline):
    if type(deadline) is not int or not 1_000_000_000<=deadline<10_000_000_000:
        raise ValueError('invalid absolute deadline')
    if set(scripts)!=set(PUBLIC_SCRIPTS) or '\nQSB_READY\n' in ready:
        raise ValueError('unexpected public source inventory')
    files=dict(scripts,**{'batch.json':batch_raw.decode()})
    payload=json.dumps(files,sort_keys=True).encode()
    encoded=base64.b64encode(gzip.compress(payload,mtime=0)).decode()
    digest=hashlib.sha256(payload).hexdigest()
    # Data is encoded; public request strings never become shell syntax.
    command=f'''set -eu
bash -s -- {deadline} <<'QSB_READY'
{ready}
QSB_READY
python3 - <<'QSB_PUBLIC_FILES'
import base64,gzip,hashlib,json,os
from pathlib import Path
raw=gzip.decompress(base64.b64decode('{encoded}'))
if hashlib.sha256(raw).hexdigest()!='{digest}':raise ValueError('payload hash mismatch')
files=json.loads(raw)
if set(files)!={{'run_fresh_sm86.py','host-a10g-fresh.sh','batch.json'}}:raise ValueError('unexpected files')
root=Path('/opt/qsb-a10g-fresh');root.mkdir()
manifest=[]
for name,content in files.items():
 with (root/name).open('x') as stream:
  stream.write(content);stream.flush();os.fsync(stream.fileno())
 manifest.append(hashlib.sha256(content.encode()).hexdigest()+'  '+name+'\\n')
(root/'SHA256SUMS').write_text(''.join(manifest))
QSB_PUBLIC_FILES
bash /opt/qsb-a10g-fresh/host-a10g-fresh.sh /opt/qsb-a10g-fresh /var/tmp/qsb-a10g-fresh-results {deadline}
'''
    if len(command.encode())>23_000:raise ValueError('public command exceeds bounded SSM payload')
    return command


def submit_once(budget, state_path, campaign, command, receipt_path, aws=aws_cli, now=time.time):
    state_path=Path(state_path).resolve();receipt_path=Path(receipt_path)
    state=load(state_path);token=state['token']
    Guard(budget,token,state_path,campaign).check(state_path,state,'submit')
    record=budget.get(token)
    if state.get('phase')!='launched' or record['state']!='attached' or state.get('instanceId')!=record['resource']['instanceId']:
        raise ValueError('exact allocated resource required')
    if type(state.get('deadline')) is not int or state['deadline']-now()<1080:
        raise ValueError('insufficient execution time remains')
    if receipt_path.exists():raise ValueError('saved command already exists; poll it')
    # This transaction commits the exact command before the only provider call.
    Journal(budget).claim_command(token,command)
    if state['deadline']-now()<1080:
        raise ValueError('deadline consumed by durable intent; reconcile without sending')
    response=aws(['ssm','send-command','--cli-input-json',json.dumps(dict(
        InstanceIds=[state['instanceId']],DocumentName='AWS-RunShellScript',
        Parameters=dict(commands=[command],executionTimeout=['1800']),TimeoutSeconds=60))])
    # Persist provider ID even if later attachment fails; never repeat submission.
    save_new(receipt_path,response)
    returned=response.get('Command',{})
    if returned.get('InstanceIds')!=[state['instanceId']] or returned.get('DocumentName')!='AWS-RunShellScript':
        raise ValueError('unexpected provider command binding; reconcile')
    Journal(budget).attach_command(token,returned['CommandId'])
    return dict(commandId=returned['CommandId'],instanceId=state['instanceId'],status='submitted')


def main():
    import argparse
    parser=argparse.ArgumentParser()
    for name in ('ledger','campaign','execution','receipt'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();campaign=load(args.campaign)
    if campaign.get('candidateSource')!=SOURCE or campaign.get('imageDigest')!=IMAGE:raise ValueError('wrong candidate')
    if aws_cli(['sts','get-caller-identity'])['Account']!='905846953990':raise ValueError('wrong AWS account')
    budget=Budget(args.ledger,campaign)
    with owner_lock(budget.path):
        commit=source_identity();state=load(args.execution)
        if state['controllerCommit']!=commit:raise ValueError('controller changed since reservation')
        with budget.transaction() as db:
            row=db.execute('SELECT batch,state FROM proof_sessions WHERE token=?',(state['token'],)).fetchone()
            if not row or row[1]!='registered':raise ValueError('session already attempted or not registered')
            batch_raw=row[0].encode()
        def committed(path):return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT,text=True)
        scripts={name:committed(path) for name,path in PUBLIC_SCRIPTS.items()}
        ready=committed('ops/aws-gpu-execution/ready.sh')
        command=build_command(batch_raw,scripts,ready,state['deadline'])
        result=submit_once(budget,args.execution,campaign,command,args.receipt)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':main()
