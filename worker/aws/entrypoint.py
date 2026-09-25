"""AWS Batch public-only transport; one input and one immutable output per job."""
import hashlib
import json
import os
import re
import time

MAX_INPUT=150000
MAX_OUTPUT=600000

def run(s3, compute, env):
    job=env['AWS_BATCH_JOB_ID']
    if not re.fullmatch(r'[a-f0-9-]{36}',job): raise ValueError('Invalid Batch job id')
    bucket=env['QSB_JOB_BUCKET'];key=env['QSB_INPUT_KEY'];digest=env['QSB_INPUT_SHA256']
    if not re.fullmatch(r'inputs/[a-f0-9-]{36}\.json',key): raise ValueError('Invalid input key')
    if not re.fullmatch(r'[a-f0-9]{64}',digest): raise ValueError('Invalid input digest')
    response=s3.get_object(Bucket=bucket,Key=key)
    body=response['Body']
    try:
        if response['ContentLength']>MAX_INPUT: raise ValueError('Input too large')
        raw=body.read(MAX_INPUT+1)
    finally: body.close()
    if len(raw)>MAX_INPUT or hashlib.sha256(raw).hexdigest()!=digest: raise ValueError('Input identity mismatch')
    event=json.loads(raw)
    if set(event)!={'input'}: raise ValueError('Unexpected envelope')
    start=time.monotonic()
    result=compute(event)
    output=json.dumps({'jobId':job,'inputSha256':digest,'executionTime':int((time.monotonic()-start)*1000),'output':result},separators=(',',':')).encode()
    if len(output)>MAX_OUTPUT: raise ValueError('Output too large')
    s3.put_object(Bucket=bucket,Key=f'outputs/{job}.json',Body=output,ContentType='application/json',IfNoneMatch='*')
    print(json.dumps({'jobId':job,'status':result.get('status'),'outputBytes':len(output)}),flush=True)

def main():
    import boto3
    from botocore.config import Config
    from handler import handler
    s3=boto3.client('s3',config=Config(connect_timeout=5,read_timeout=15,retries={'mode':'standard','total_max_attempts':1}))
    run(s3,handler,os.environ)

if __name__=='__main__':main()
