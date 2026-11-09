"""Operate one existing scoped execution. Usage: operate.py STATE_DIRECTORY MODE.

No replacement submissions or new infrastructure are created by this adapter.
"""
import json,pathlib,subprocess,sys,hashlib,time,os
if not __debug__: raise RuntimeError("Run this operator without Python optimization")
from ssm_command import bash_command, decode_result
from chunk_results import collect
p=pathlib.Path(sys.argv[1]).resolve()
s=json.loads((p/'execution.json').read_text());config=json.loads((p/'operator.json').read_text())
assert s['operatorConfig']==config

def save(name,data):
 with (p/name).open('x') as f:json.dump(data,f,indent=2);f.flush();os.fsync(f.fileno())
def aws(*args):
 return json.loads(subprocess.check_output(['aws','--profile',config['profile'],'--region',config['region'],'--output','json',*args],text=True,timeout=60,env={**os.environ,'AWS_MAX_ATTEMPTS':'1'}))
assert aws('sts','get-caller-identity')['Account']==config['account']
mode=sys.argv[2]
if mode=='record':
 r=aws('ec2','describe-instances','--instance-ids',s['instanceId']);i=r['Reservations'][0]['Instances'][0];assert i['ClientToken']==s['token'];assert i['InstanceType']=='g5.xlarge'
 s['volumeIds']=[x['Ebs']['VolumeId'] for x in i['BlockDeviceMappings']];assert s['volumeIds'];save('allocated.json',r)
 (p/'execution.json').write_text(json.dumps(s,indent=2));print(i['State']['Name'])
elif mode=='ready':
 r=aws('ssm','describe-instance-information','--filters',json.dumps([{'Key':'InstanceIds','Values':[s['instanceId']]}]));print(json.dumps(r))
elif mode=='send':
 assert time.time()+1080<s['deadline'];assert not (p/'send-intent.json').exists()
 command=bash_command((p/'host-template.sh').read_text().replace('__DEADLINE__',str(s['deadline'])))
 req={'InstanceIds':[s['instanceId']],'DocumentName':'AWS-RunShellScript','Parameters':{'commands':[command],'executionTimeout':['1200']},'TimeoutSeconds':60}
 save('send-intent.json',{'request':req,'sha256':hashlib.sha256(command.encode()).hexdigest()})
 r=aws('ssm','send-command','--cli-input-json',json.dumps(req));save('send-response.json',r);print(r['Command']['CommandId'])
elif mode=='poll':
 cid=json.loads((p/'send-response.json').read_text())['Command']['CommandId'];r=aws('ssm','get-command-invocation','--command-id',cid,'--instance-id',s['instanceId'])
 assert r['CommandId']==cid and r['InstanceId']==s['instanceId'];print(r['Status'])
 if r['Status'] in ['Success','Failed','Cancelled','TimedOut']:
  save('terminal.json',r)
  out=r['StandardOutputContent']; print(out[-2000:]); print(r['StandardErrorContent'][-1000:])
  try:
   if 'QSB_PUBLIC_RESULT_META=' in out:
    value=collect(p/'chunks',s['instanceId'],out,aws,s['deadline'])
   else:
    value=decode_result(out)
   save('public-results.json',value)
  except Exception as error:
   save('collection-error.json',{'error':str(error),'ssmStatus':r['Status'],'responseCode':r['ResponseCode']})
   print('Result collection failed; raw terminal evidence retained')
  finally:
   save('terminate-response.json',aws('ec2','terminate-instances','--instance-ids',s['instanceId']))
elif mode=='terminate':
 print(json.dumps(aws('ec2','terminate-instances','--instance-ids',s['instanceId'])))
