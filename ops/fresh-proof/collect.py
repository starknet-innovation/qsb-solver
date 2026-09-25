"""Resumable SSM reads of public proof results; never submits solver work."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
from results import assemble_chunks, persist_collection, unique_object

REMOTE = '/var/tmp/qsb-a10g-fresh-results/public-result.b64'
CHUNK = 18000
PENDING = {'Pending','InProgress','Delayed','Cancelling'}


def save_new(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, sort_keys=True)
        stream.flush(); os.fsync(stream.fileno())
    fd = os.open(path.parent, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def invocation(aws, command, instance):
    response = aws(['ssm','get-command-invocation','--command-id',command,'--instance-id',instance])
    if response.get('CommandId') != command or response.get('InstanceId') != instance:
        raise ValueError('SSM invocation identity mismatch')
    return response


def collect_once(root, instance, command, batch_raw, aws, validate_batch, validate_binding, work_range):
    if not re.fullmatch('i-[0-9a-f]{17}', instance) or not re.fullmatch('[0-9a-f-]{36}', command):
        raise ValueError('Invalid saved execution identity')
    root = Path(root)
    root.mkdir(exist_ok=True)
    fd = os.open(root.parent, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)
    # Single local collector; a resumed call polls saved command IDs, not new work.
    with (root/'collector.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        context = dict(instanceId=instance, commandId=command,
                       batchSha256=hashlib.sha256(batch_raw).hexdigest())
        if (root/'context.json').exists():
            if load(root/'context.json') != context: raise ValueError('Collection context changed')
        else:
            save_new(root/'context.json', context)
        if (root/'evidence').exists():
            raise ValueError('Evidence directory already exists; inspect its receipt, never overwrite')
        original = invocation(aws, command, instance)
        if original.get('Status') in PENDING:
            return dict(status='waiting-for-original-command', commandId=command)
        if original.get('Status') not in {'Success','Failed','TimedOut','Cancelled'}:
            raise ValueError('Unknown original SSM state')
        lines = [line.split('=',1)[1] for line in original.get('StandardOutputContent','').splitlines()
                 if line.startswith('QSB_PUBLIC_RESULT_META=')]
        if len(lines) != 1: raise ValueError('Missing or ambiguous archive receipt; reconcile original session')
        meta = json.loads(lines[0], object_pairs_hook=unique_object)
        if (set(meta) != {'bytes','sha256'} or type(meta['bytes']) is not int
                or not 0 < meta['bytes'] <= 2_000_000
                or not re.fullmatch('[0-9a-f]{64}', meta['sha256'])):
            raise ValueError('Invalid archive receipt')
        if (root/'metadata.json').exists():
            if load(root/'metadata.json') != meta: raise ValueError('Original archive changed')
        else:
            save_new(root/'metadata.json', meta)
        if not (root/'original-invocation.json').exists():
            save_new(root/'original-invocation.json', original)
        chunks = []
        for offset in range(0, meta['bytes'], CHUNK):
            count = min(CHUNK, meta['bytes']-offset)
            prefix = root / str(offset)
            intent = prefix.with_suffix('.intent.json')
            receipt = prefix.with_suffix('.command.json')
            result_file = prefix.with_suffix('.result.json')
            code = ('import pathlib,sys;d=pathlib.Path('+repr(REMOTE)+').read_bytes();'
                    f'sys.stdout.write(d[{offset}:{offset+count}].decode("ascii"))')
            request = dict(InstanceIds=[instance], DocumentName='AWS-RunShellScript',
                           Parameters=dict(commands=['python3 -c '+shlex.quote(code)],executionTimeout=['30']),
                           TimeoutSeconds=60)
            if intent.exists():
                if load(intent) != request: raise ValueError('Chunk read intent changed')
                if not receipt.exists():
                    raise ValueError('Uncertain SSM read submission; do not resubmit')
            else:
                if receipt.exists() or result_file.exists(): raise ValueError('Orphaned read evidence')
                save_new(intent, request)
                reply = aws(['ssm','send-command','--cli-input-json',json.dumps(request)])
                cid = reply.get('Command',{}).get('CommandId','')
                if not re.fullmatch('[0-9a-f-]{36}',cid): raise ValueError('Uncertain SSM read identity')
                save_new(receipt, dict(commandId=cid,instanceId=instance))
            saved = load(receipt)
            if saved.get('instanceId') != instance: raise ValueError('Saved read instance mismatch')
            cid = saved['commandId']
            response = load(result_file) if result_file.exists() else invocation(aws,cid,instance)
            if response.get('CommandId') != cid or response.get('InstanceId') != instance:
                raise ValueError('Saved read identity mismatch')
            if response.get('Status') in PENDING:
                return dict(status='waiting-for-chunk',commandId=cid,offset=offset)
            if response.get('Status') != 'Success' or response.get('ResponseCode') != 0:
                raise ValueError('Public chunk read failed; reconcile without replacement')
            chunk = response.get('StandardOutputContent','').encode('ascii')
            if len(chunk) != count: raise ValueError('Truncated public chunk')
            if not result_file.exists(): save_new(result_file,response)
            chunks.append((offset,chunk))
        encoded = assemble_chunks(chunks,meta)
        return persist_collection(root/'evidence',encoded,meta,batch_raw,validate_batch,validate_binding,work_range)


def aws_cli(parts):
    # send-command has no client token: SDK retries would violate our one-shot intent.
    env = dict(os.environ, AWS_MAX_ATTEMPTS='1', AWS_RETRY_MODE='standard')
    return json.loads(subprocess.check_output(['aws','--profile','snf','--region','eu-west-1',
        '--output','json','--cli-connect-timeout','10','--cli-read-timeout','40']+parts,
        text=True,timeout=60,env=env))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--execution',type=Path,required=True)
    parser.add_argument('--command',type=Path,required=True,help='Saved original host send-command response')
    parser.add_argument('--batch',type=Path,required=True)
    parser.add_argument('--collection',type=Path,required=True)
    args=parser.parse_args()
    aws = aws_cli
    if aws(['sts','get-caller-identity'])['Account'] != '905846953990':
        raise ValueError('Wrong AWS account')
    repo=Path(__file__).resolve().parents[2]
    spec=importlib.util.spec_from_file_location('fresh_sm86',repo/'worker/promotion/validation/run_fresh_sm86.py')
    runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
    sys.path.insert(0,str(repo/'worker'))
    from search_ranges import work_range
    state=load(args.execution);command=load(args.command)['Command']['CommandId']
    if state.get('phase') != 'launched': raise ValueError('Expected saved launched execution')
    result=collect_once(args.collection,state['instanceId'],command,args.batch.read_bytes(),aws,
                        runner.validate_batch,runner.validate_binding,work_range)
    print(json.dumps(result,sort_keys=True))


if __name__ == '__main__': main()
