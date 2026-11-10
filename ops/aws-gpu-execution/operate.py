"""Operate one existing scoped execution. Usage: operate.py STATE_DIRECTORY MODE.

No replacement submissions or new infrastructure are created by this adapter.
"""
import json,pathlib,subprocess,sys,hashlib,time,os
if not __debug__: raise RuntimeError("Run this operator without Python optimization")
from ssm_command import bash_command, decode_result
from chunk_results import collect
MODES=('record','ready','send','poll','terminate')
MIN_SEND_SECONDS=2160  # host gate minimum (1,500 s) plus a 660 s staging reserve; control.py launch allows for this
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
 volumes=[x['Ebs']['VolumeId'] for x in i['BlockDeviceMappings']];assert volumes
 # Resume after an interruption between the receipt and the state update, but only for the same allocation.
 kept=save_once('allocated.json',r)['Reservations'][0]['Instances'][0]
 if kept['InstanceId']!=s['instanceId'] or kept['ClientToken']!=s['token'] or [x['Ebs']['VolumeId'] for x in kept['BlockDeviceMappings']]!=volumes:
  raise ValueError('existing allocation receipt is for a different allocation')
 s['volumeIds']=volumes;replace_state(s);print(i['State']['Name'])
elif mode=='ready':
 # SSM registration only. It is not host readiness: the staged host command must still run ready.sh,
 # which checks the boot marker and shutdown timer, before any compute. Exit non-zero unless online.
 r=aws('ssm','describe-instance-information','--filters',json.dumps([{'Key':'InstanceIds','Values':[s['instanceId']]}]));print(json.dumps(r))
 rows=r.get('InstanceInformationList',[])
 if len(rows)!=1 or rows[0].get('InstanceId')!=s['instanceId'] or rows[0].get('PingStatus')!='Online':raise SystemExit(3)
elif mode=='send':
 # The host gate needs 1,500 s when it starts. Before it, the sent command itself stages on the host:
 # a 120 s archive download, up to eleven 30 s runner-file fetches and a 180 s readiness wait, 630 s,
 # reserved as 660 s. That staging runs after this check, inside the command, so it is part of
 # MIN_SEND_SECONDS; rendering the template on the operator side beforehand takes seconds.
 assert time.time()+MIN_SEND_SECONDS<s['deadline'];assert not (p/'send-intent.json').exists()
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
  # Only a successful command with a collected result is a success. Termination above has already
  # been requested; the exit status must not let automation treat anything else as a passed gate.
  if (p/'collection-error.json').exists() or not (p/'public-results.json').exists():raise SystemExit(4)
  if r['Status']!='Success' or r.get('ResponseCode')!=0:raise SystemExit(5)
elif mode=='terminate':
 print(json.dumps(aws('ec2','terminate-instances','--instance-ids',s['instanceId'])))
