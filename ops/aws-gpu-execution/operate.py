"""Operate one existing scoped execution. Usage: operate.py STATE_DIRECTORY MODE.

No replacement submissions or new infrastructure are created by this adapter.
"""
import json,pathlib,subprocess,sys,hashlib,time,os
if not __debug__: raise RuntimeError("Run this operator without Python optimization")
from ssm_command import bash_command, decode_result
from chunk_results import collect
MODES=('record','ready','send','poll','terminate')
# A mistyped mode must fail loudly before any call: a silent no-op could leave a paid instance running.
if len(sys.argv)!=3 or sys.argv[2] not in MODES:raise SystemExit('usage: operate.py STATE_DIRECTORY {'+'|'.join(MODES)+'}')
p=pathlib.Path(sys.argv[1]).resolve()
s=json.loads((p/'execution.json').read_text());config=json.loads((p/'operator.json').read_text())
assert s['operatorConfig']==config

def save(name,data):
 with (p/name).open('x') as f:json.dump(data,f,indent=2);f.flush();os.fsync(f.fileno())
 # The directory entry must be durable too: a lost send intent could allow a second submission.
 fd=os.open(p,os.O_RDONLY)
 try:os.fsync(fd)
 finally:os.close(fd)
def replace_state(state):
 # execution.json holds the token and every temporary resource identity that cleanup needs.
 # Replace it atomically so an interrupted write can never leave it truncated.
 tmp=p/'execution.json.tmp'
 with tmp.open('w') as f:json.dump(state,f,indent=2);f.flush();os.fsync(f.fileno())
 os.replace(tmp,p/'execution.json')
 fd=os.open(p,os.O_RDONLY)
 try:os.fsync(fd)
 finally:os.close(fd)
def save_once(name,data):
 # A rerun after an interrupted terminal step must resume, not fail on a receipt that already exists.
 if (p/name).exists():return json.loads((p/name).read_text())
 save(name,data);return data
def aws(*args):
 return json.loads(subprocess.check_output(['aws','--profile',config['profile'],'--region',config['region'],'--output','json',*args],text=True,timeout=60,env={**os.environ,'AWS_MAX_ATTEMPTS':'1'}))
assert aws('sts','get-caller-identity')['Account']==config['account']
mode=sys.argv[2]
if mode=='record':
 r=aws('ec2','describe-instances','--instance-ids',s['instanceId']);i=r['Reservations'][0]['Instances'][0];assert i['ClientToken']==s['token'];assert i['InstanceType']=='g5.xlarge'
 s['volumeIds']=[x['Ebs']['VolumeId'] for x in i['BlockDeviceMappings']];assert s['volumeIds'];save('allocated.json',r)
 replace_state(s);print(i['State']['Name'])
elif mode=='ready':
 r=aws('ssm','describe-instance-information','--filters',json.dumps([{'Key':'InstanceIds','Values':[s['instanceId']]}]));print(json.dumps(r))
elif mode=='send':
 # The host gate needs 1,080 s when it starts, after staging (archive download, runner files, readiness).
 # Reserve 420 s for that staging so an accepted one-shot command is not rejected on the host.
 assert time.time()+1500<s['deadline'];assert not (p/'send-intent.json').exists()
 # The staging step records the digest of the template it rendered. Refuse a template that is missing
 # that record or no longer matches it, so an edited or replaced file is never executed remotely.
 template=(p/'host-template.sh').read_bytes();expected=(p/'host-template.sh.sha256').read_text().split()
 if len(expected)!=1 or hashlib.sha256(template).hexdigest()!=expected[0]:raise ValueError('host template does not match its staged digest')
 command=bash_command(template.decode().replace('__DEADLINE__',str(s['deadline'])))
 # The host script's own limits (downloads, readiness, image pull, gate) can add up to about 30 minutes.
 # SSM must not cut it short; the absolute instance deadline remains the hard bound.
 execution_timeout=min(1800,int(s['deadline']-time.time())-60)
 req={'InstanceIds':[s['instanceId']],'DocumentName':'AWS-RunShellScript','Parameters':{'commands':[command],'executionTimeout':[str(execution_timeout)]},'TimeoutSeconds':60}
 save('send-intent.json',{'request':req,'sha256':hashlib.sha256(command.encode()).hexdigest()})
 r=aws('ssm','send-command','--cli-input-json',json.dumps(req));save('send-response.json',r);print(r['Command']['CommandId'])
elif mode=='poll':
 cid=json.loads((p/'send-response.json').read_text())['Command']['CommandId'];r=aws('ssm','get-command-invocation','--command-id',cid,'--instance-id',s['instanceId'])
 assert r['CommandId']==cid and r['InstanceId']==s['instanceId'];print(r['Status'])
 if r['Status'] in ['Success','Failed','Cancelled','TimedOut']:
  kept=save_once('terminal.json',r)
  if (kept['CommandId'],kept['InstanceId'],kept['Status'])!=(r['CommandId'],r['InstanceId'],r['Status']):raise ValueError('terminal receipt differs from the command state')
  r=kept;out=r['StandardOutputContent']; print(out[-2000:]); print(r['StandardErrorContent'][-1000:])
  try:
   if not (p/'public-results.json').exists():
    if 'QSB_PUBLIC_RESULT_META=' in out:
     value=collect(p/'chunks',s['instanceId'],out,aws,s['deadline'])
    else:
     value=decode_result(out)
    save('public-results.json',value)
  except Exception as error:
   save_once('collection-error.json',{'error':str(error),'ssmStatus':r['Status'],'responseCode':r['ResponseCode']})
   print('Result collection failed; raw terminal evidence retained')
  finally:
   # Termination is idempotent: always request it, keep the first response.
   save_once('terminate-response.json',aws('ec2','terminate-instances','--instance-ids',s['instanceId']))
elif mode=='terminate':
 print(json.dumps(aws('ec2','terminate-instances','--instance-ids',s['instanceId'])))
