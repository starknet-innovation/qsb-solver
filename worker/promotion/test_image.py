"""Offline combined-image contract checks; successful GPU execution is a separate gate."""
import json
import subprocess
import sys
image = sys.argv[1]
code = '''import base64,hashlib,json,pathlib,handler
b=handler.release_binding()
assert b['status']=='HOLD'
assert not pathlib.Path('/opt/qsb/cpu').exists()
raw=b'public synthetic parameter bytes'*4
request={'protocol':'qsb-config-a-v1','stage':'round1','parameterBase64':base64.b64encode(raw).decode(),'parameterSha256':hashlib.sha256(raw).hexdigest(),'manifestHash':'a'*64,'attempt':0,'sequence':2147483648,'locktime':500000000,'kernelCommit':b['solverCommit'],'searchVersion':'ranked-v2'}
try: handler.handler({'input':dict(request, kernelCommit='0'*40)})
except ValueError: pass
else: raise AssertionError('Wrong release accepted')
for stage in ('pinning','round1','round2'):
    result=handler.handler({'input':dict(request,stage=stage)})
    assert result['status']=='failed', result
    assert result['checkpoint']=='requires-verification-or-resume', result
    assert result['kernelCommit']==b['solverCommit']
print(json.dumps(b))
'''
subprocess.run(['docker','run','--rm','--network','none','--read-only',
                '--tmpfs','/tmp:rw,nosuid,size=128m','--entrypoint','python3',image,'-c',code],check=True)
