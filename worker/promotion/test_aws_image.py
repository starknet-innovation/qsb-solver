"""Offline real AWS entrypoint-to-combined-handler gate. No AWS calls or GPU."""
import json
import subprocess
import sys

image = sys.argv[1]
config = json.loads(subprocess.check_output(['docker', 'inspect', image], text=True))[0]['Config']
if config['Cmd'] != ['python3', 'aws_entrypoint.py']:
    raise ValueError('AWS image does not start the Batch entrypoint')
code = '''import base64,hashlib,io,json,aws_entrypoint,handler,boto3
binding=handler.release_binding()
assert binding['architecture']=='sm_86'
job='12345678-1234-1234-1234-123456789abc'
class S3:
    def __init__(self, raw): self.raw=raw; self.output=None
    def get_object(self, **kwargs):
        assert kwargs==dict(Bucket='public-test',Key='inputs/'+job+'.json')
        return dict(ContentLength=len(self.raw),Body=io.BytesIO(self.raw))
    def put_object(self, **kwargs):
        assert kwargs['Bucket']=='public-test' and kwargs['Key']=='outputs/'+job+'.json'
        assert kwargs['IfNoneMatch']=='*'
        assert self.output is None
        self.output=json.loads(kwargs['Body'])
raw=b'public synthetic parameters'*4
for stage in ('pinning','round1','round2'):
    request=dict(protocol='qsb-config-a-v1',stage=stage,parameterBase64=base64.b64encode(raw).decode(),parameterSha256=hashlib.sha256(raw).hexdigest(),manifestHash='a'*64,attempt=0,sequence=2147483648,locktime=500000000,kernelCommit=binding['solverCommit'],searchVersion='ranked-v2')
    data=json.dumps(dict(input=request)).encode()
    s3=S3(data)
    env=dict(AWS_BATCH_JOB_ID=job,QSB_JOB_BUCKET='public-test',QSB_INPUT_KEY='inputs/'+job+'.json',QSB_INPUT_SHA256=hashlib.sha256(data).hexdigest())
    aws_entrypoint.run(s3,handler.handler,env)
    result=s3.output['output']
    assert result['kernelCommit']==binding['solverCommit']
    assert result['status']=='failed' and result['checkpoint']=='requires-verification-or-resume'
    assert s3.output['inputSha256']==env['QSB_INPUT_SHA256']
    s3=S3(data)
    try: aws_entrypoint.run(s3,handler.handler,dict(env,QSB_INPUT_SHA256='0'*64))
    except ValueError: pass
    else: raise AssertionError('Tampered input accepted')
    assert s3.output is None
'''
subprocess.run(['docker','run','--rm','--network','none','--read-only',
                '--tmpfs','/tmp:rw,nosuid,size=128m','--entrypoint','python3',image,'-c',code],check=True)
