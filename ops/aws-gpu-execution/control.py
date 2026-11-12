"""One-shot benchmark infrastructure; all state stays outside the repository."""
import argparse
import base64
from datetime import datetime, timedelta, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import uuid
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'ops/aws-gpu-benchmark'))
from launch import boot_script
sys.path.append(str(Path(__file__).resolve().parent))
from operator_config import load_config, expected_account
_ACTIVE_CONFIG = None
SINGLE_A10G = ('g5.xlarge', 'g5.2xlarge', 'g5.4xlarge', 'g5.8xlarge', 'g5.16xlarge')


def qualified_shape(call, instance_type, quota):
    if instance_type not in SINGLE_A10G:
        raise ValueError('Only reviewed single-A10G sizes are supported')
    shape = call('ec2', 'describe-instance-types', InstanceTypes=[instance_type])['InstanceTypes'][0]
    gpus = shape.get('GpuInfo', {}).get('Gpus', [])
    if (shape['InstanceType'] != instance_type or len(gpus) != 1 or gpus[0].get('Name') != 'A10G'
            or gpus[0].get('Count') != 1 or 'x86_64' not in shape['ProcessorInfo']['SupportedArchitectures']):
        raise ValueError('Unexpected native GPU/architecture')
    if quota < shape['VCpuInfo']['DefaultVCpus']:
        raise ValueError('Quota not effective for selected size')
    return shape


def placement_options(call, config, automatic):
    if not automatic:
        return {'SubnetId':config['subnet']}
    vpcs=call('ec2','describe-vpcs',VpcIds=[config['vpc']])['Vpcs']
    subnets=call('ec2','describe-subnets',Filters=[{'Name':'vpc-id','Values':[config['vpc']]},
                 {'Name':'default-for-az','Values':['true']}])['Subnets']
    if (len(vpcs)!=1 or vpcs[0]['VpcId']!=config['vpc'] or not vpcs[0].get('IsDefault')
            or not subnets or any(s['VpcId']!=config['vpc'] or not s.get('DefaultForAz')
                                    or not s.get('MapPublicIpOnLaunch') for s in subnets)):
        raise ValueError('Automatic placement requires the verified default VPC and public default subnets')
    # RunInstances chooses a default subnet when none is supplied. The explicit no-ingress
    # security-group ID still pins the verified VPC. Record actual subnet/AZ after launch.
    return {}


def aws(service, operation, **request):
    config=load_config()
    if _ACTIVE_CONFIG is not None and config != _ACTIVE_CONFIG:
        raise ValueError('Operator configuration changed during execution')
    if os.environ.get('QSB_AWS_MCP_RPC_DIR'):
        from mcp_rpc import exchange
        return exchange(os.environ['QSB_AWS_MCP_RPC_DIR'], config['region'], service, operation, request)
    result=subprocess.run(['aws','--profile',config['profile'],'--region',config['region'],'--output','json',
        '--no-cli-pager',service,operation,'--cli-input-json',json.dumps(request)],
        capture_output=True,text=True,env={**os.environ,'AWS_MAX_ATTEMPTS':'1'},timeout=90)
    if result.returncode:
        raise RuntimeError(f'{service} {operation}: {result.stderr}')
    return json.loads(result.stdout) if result.stdout.strip() else {}


def save(path,state):
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2)+'\n');tmp.replace(path)


def cleanup_archive(directory):
    """The cleanup function's ZIP, byte-for-byte the same on every call so it can be staged before arm."""
    archive=Path(directory)/'cleanup.zip'
    info=zipfile.ZipInfo('cleanup.py',date_time=(1980,1,1,0,0,0));info.external_attr=0o644<<16
    with zipfile.ZipFile(archive,'w') as z: z.writestr(info,Path(__file__).with_name('cleanup.py').read_bytes())
    return archive


def function_code(archive,environ):
    """The Code parameter exactly as it will be sent, so the persisted request is the request made.

    The local CLI takes the ZIP inline. The MCP handoff corrupts inline ZIP bytes, so there the
    archive must already be staged in S3 and the request names that object; CreateFunction's
    CodeSha256 is then checked against the local archive either way."""
    if not environ.get('QSB_AWS_MCP_RPC_DIR'):
        return {'ZipFile':base64.b64encode(Path(archive).read_bytes()).decode()}
    bucket,key=environ.get('QSB_CLEANUP_CODE_S3_BUCKET'),environ.get('QSB_CLEANUP_CODE_S3_KEY')
    if not bucket or not key:
        raise ValueError('MCP mode needs the staged cleanup archive: set QSB_CLEANUP_CODE_S3_BUCKET and QSB_CLEANUP_CODE_S3_KEY')
    return {'S3Bucket':bucket,'S3Key':key}


def policy(statements):
    return json.dumps({'Version':'2012-10-17','Statement':statements})


def trust(service):
    return policy([{'Effect':'Allow','Principal':{'Service':service},'Action':'sts:AssumeRole'}])


def role(name,principal,document):
    aws('iam','create-role',RoleName=name,AssumeRolePolicyDocument=trust(principal))
    aws('iam','put-role-policy',RoleName=name,PolicyName='benchmark-only',PolicyDocument=document)


def main():
    global _ACTIVE_CONFIG
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['prepare','arm','launch','cleanup'])
    parser.add_argument('--state',type=Path,required=True)
    parser.add_argument('--instance-type',choices=SINGLE_A10G)
    parser.add_argument('--session-minutes',type=int,choices=(25,60))
    parser.add_argument('--auto-default-subnet',action='store_true')
    args=parser.parse_args();path=args.state
    if (args.instance_type is not None or args.session_minutes is not None or args.auto_default_subnet) and args.mode != 'prepare':
        parser.error('Session size and duration are recorded at prepare only')
    config=load_config()
    _ACTIVE_CONFIG=dict(config)
    ACCOUNT,REGION,AMI,SUBNET,VPC=(config[k] for k in ('account','region','ami','subnet','vpc'))
    if aws('sts','get-caller-identity')['Account']!=ACCOUNT: raise ValueError('Wrong account')
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT): raise ValueError('Dirty checkout')
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    remote=subprocess.check_output(['git','rev-parse','@{upstream}'],cwd=ROOT,text=True).strip()
    if commit!=remote: raise ValueError('Source not pushed')
    if args.mode=='prepare':
        if path.exists(): raise ValueError('Existing experiment: reconcile state')
        token=str(uuid.uuid4());name='qsb-bench-'+token[:8]
        s={'token':token,'name':name,'controllerCommit':commit,'phase':'preparing','operatorConfig':config,
           'instanceType':args.instance_type or 'g5.xlarge','sessionMinutes':args.session_minutes or 25,
           'autoDefaultSubnet':args.auto_default_subnet}
        path.parent.mkdir(parents=True,exist_ok=True);save(path,s)
        role(name+'-host','ec2.amazonaws.com',(ROOT/'ops/aws-gpu-benchmark/instance-policy.json').read_text())
        aws('iam','create-instance-profile',InstanceProfileName=name)
        aws('iam','add-role-to-instance-profile',InstanceProfileName=name,RoleName=name+'-host')
        s['securityGroup']=aws('ec2','create-security-group',GroupName=name,Description='Isolated QSB benchmark; no inbound',VpcId=VPC)['GroupId'];save(path,s)
        role(name+'-cleanup','lambda.amazonaws.com',policy([
            {'Effect':'Allow','Action':'ec2:DescribeInstances','Resource':'*'},
            {'Effect':'Allow','Action':'ec2:TerminateInstances','Resource':f'arn:aws:ec2:{REGION}:{ACCOUNT}:instance/*',
             'Condition':{'StringEquals':{'ec2:ResourceTag/QsbBenchmarkToken':token}}}]))
        function_arn=f'arn:aws:lambda:{REGION}:{ACCOUNT}:function:{name}'
        schedule_trust=policy([{'Effect':'Allow','Principal':{'Service':'scheduler.amazonaws.com'},'Action':'sts:AssumeRole',
            'Condition':{'StringEquals':{'aws:SourceAccount':ACCOUNT},'ArnEquals':{'aws:SourceArn':f'arn:aws:scheduler:{REGION}:{ACCOUNT}:schedule-group/default'}}}])
        aws('iam','create-role',RoleName=name+'-schedule',AssumeRolePolicyDocument=schedule_trust)
        aws('iam','put-role-policy',RoleName=name+'-schedule',PolicyName='benchmark-only',PolicyDocument=policy([
            {'Effect':'Allow','Action':'lambda:InvokeFunction','Resource':function_arn}]))
        # The archive exists from here, with its hash, so an MCP operator can stage those exact bytes before arm.
        archive=cleanup_archive(path.parent)
        s.update(phase='prepared',functionArn=function_arn,cleanupCodeSha256=base64.b64encode(hashlib.sha256(archive.read_bytes()).digest()).decode());save(path,s)
    else:
        s=json.loads(path.read_text());name=s['name']
        if s.get('operatorConfig') != config:
            raise ValueError('Operator scope changed or legacy state: reconcile explicitly')
        if s['controllerCommit']!=commit:
            if args.mode!='cleanup': raise ValueError('Controller commit changed: reconcile first')
            subprocess.run(['git','merge-base','--is-ancestor',s['controllerCommit'],commit],cwd=ROOT,check=True)
            s['cleanupControllerCommit']=commit
        if args.mode=='arm':
            if s['phase']!='prepared': raise ValueError('Already armed or launched')
            # Start the fixed deadline before launch. Repeating arm is forbidden.
            # Build the archive and settle how its code is delivered before the deadline starts: a
            # missing staged object must not burn the one arm.
            archive=cleanup_archive(path.parent)
            code=function_code(archive,os.environ)
            deadline=datetime.now(timezone.utc)+timedelta(minutes=s.get('sessionMinutes',25))
            s.update(deadline=int(deadline.timestamp()),phase='arming');save(path,s)
            actual=aws('lambda','create-function',FunctionName=name,Runtime='python3.12',
                Role=f'arn:aws:iam::{ACCOUNT}:role/{name}-cleanup',Handler='cleanup.handler',Timeout=60,
                Code=code,
                Environment={'Variables':{'RUN_TOKEN':s['token'],'DEADLINE':str(s['deadline'])}})
            if actual['CodeSha256']!=base64.b64encode(hashlib.sha256(archive.read_bytes()).digest()).decode(): raise ValueError('Lambda source mismatch')
            active_deadline=time.monotonic()+120
            while True:
                function=aws('lambda','get-function-configuration',FunctionName=name)
                if function.get('State')=='Active': break
                if function.get('State')=='Failed' or time.monotonic()>=active_deadline:
                    raise ValueError('Cleanup function did not become active')
                time.sleep(2)
            expected={'Name':name,'GroupName':'default','ScheduleExpression':f'at({(deadline+timedelta(minutes=1)).replace(second=0,microsecond=0):%Y-%m-%dT%H:%M:%S})',
                'ScheduleExpressionTimezone':'UTC','FlexibleTimeWindow':{'Mode':'OFF'},'State':'ENABLED','ActionAfterCompletion':'DELETE',
                'Target':{'Arn':s['functionArn'],'RoleArn':f'arn:aws:iam::{ACCOUNT}:role/{name}-schedule','Input':'{}',
                          'RetryPolicy':{'MaximumEventAgeInSeconds':300,'MaximumRetryAttempts':3}}}
            aws('scheduler','create-schedule',**expected)
            actual=aws('scheduler','get-schedule',Name=name,GroupName='default')
            for k,v in expected.items():
                if actual[k]!=v: raise ValueError('Schedule mismatch '+k)
            s.update(phase='armed',schedule=expected);save(path,s)
        elif args.mode=='launch':
            if s['phase']!='armed': raise ValueError('Launch intent exists or cleanup unarmed')
            if s['deadline']-time.time()<(s.get('sessionMinutes',25)-5)*60: raise ValueError('Insufficient time before deadline')
            quota=aws('service-quotas','get-service-quota',ServiceCode='ec2',QuotaCode='L-DB2E81BA')['Quota']['Value']
            instance_type=s.get('instanceType','g5.xlarge')
            s['hardware']=qualified_shape(aws,instance_type,quota);save(path,s)
            if aws('ec2','describe-instances',Filters=[{'Name':'tag:QsbBenchmarkToken','Values':[s['token']]}])['Reservations']: raise ValueError('Existing launch')
            actual=aws('scheduler','get-schedule',Name=name,GroupName='default')
            for k,v in s['schedule'].items():
                if actual[k]!=v: raise ValueError('Schedule changed')
            image=aws('ec2','describe-images',ImageIds=[AMI])['Images'][0]
            if image['Architecture']!='x86_64' or image['OwnerId']!='898082745236': raise ValueError('Unexpected AMI')
            groups=aws('ec2','describe-security-groups',GroupIds=[s['securityGroup']])['SecurityGroups']
            if groups[0]['IpPermissions']: raise ValueError('Ingress forbidden')
            if groups[0]['VpcId']!=VPC: raise ValueError('Security group VPC differs')
            placement=placement_options(aws,config,s.get('autoDefaultSubnet',False))
            # Guest timer shares the prearmed deadline, even if boot is delayed.
            start=datetime.fromtimestamp(s['deadline'],timezone.utc)-timedelta(minutes=55)
            user_data=boot_script(start)
            if s.get('sessionMinutes',25)==60:
                user_data=user_data.replace('/sbin/shutdown -h +55','/sbin/shutdown -h +60')
            request={'ImageId':AMI,'InstanceType':instance_type,'MinCount':1,'MaxCount':1,'ClientToken':s['token'],
                **placement,'SecurityGroupIds':[s['securityGroup']], 'IamInstanceProfile':{'Name':name},
                'InstanceInitiatedShutdownBehavior':'terminate','DisableApiTermination':False,
                'MetadataOptions':{'HttpTokens':'required','HttpPutResponseHopLimit':1},'UserData':user_data,
                'BlockDeviceMappings':[{'DeviceName':image['RootDeviceName'],'Ebs':{'VolumeSize':80,'VolumeType':'gp3','Encrypted':True,'DeleteOnTermination':True}}],
                'TagSpecifications':[{'ResourceType':'instance','Tags':[{'Key':'Name','Value':name},{'Key':'QsbBenchmarkToken','Value':s['token']},{'Key':'SourceCommit','Value':commit}]}]}
            s.update(phase='launch-intent',request=request);save(path,s)
            instance=aws('ec2','run-instances',**request)['Instances'][0]
            s.update(phase='launched',instanceId=instance['InstanceId'],launchTime=instance['LaunchTime'],
                     actualSubnet=instance.get('SubnetId'),actualPlacement=instance.get('Placement'));save(path,s)
        elif args.mode=='cleanup':
            instances=[i for r in aws('ec2','describe-instances',Filters=[{'Name':'tag:QsbBenchmarkToken','Values':[s['token']]}])['Reservations'] for i in r['Instances']]
            for i in instances:
                if i['State']['Name']!='terminated':
                    aws('ec2','terminate-instances',InstanceIds=[i['InstanceId']])
                    raise RuntimeError('Termination requested; rerun cleanup after EC2 reaches terminated')
            volumes=aws('ec2','describe-volumes',Filters=[{'Name':'attachment.instance-id','Values':[i['InstanceId'] for i in instances]}])['Volumes'] if instances else []
            if volumes: raise ValueError('Attached volumes remain')
            # Caller also checks recorded volume IDs for detached/orphaned volumes.
            for volume_id in s.get('volumeIds',[]):
                found=aws('ec2','describe-volumes',Filters=[{'Name':'volume-id','Values':[volume_id]}])['Volumes']
                if found: raise ValueError('Recorded volume still exists')
            schedules=aws('scheduler','list-schedules',NamePrefix=name)['Schedules']
            for schedule in schedules:
                if schedule['Name']==name: aws('scheduler','delete-schedule',Name=name,GroupName='default')
            functions=aws('lambda','list-functions')['Functions']
            if any(f['FunctionName']==name for f in functions): aws('lambda','delete-function',FunctionName=name)
            aws('iam','remove-role-from-instance-profile',InstanceProfileName=name,RoleName=name+'-host')
            aws('iam','delete-instance-profile',InstanceProfileName=name)
            for suffix in ['-host','-cleanup','-schedule']:
                aws('iam','delete-role-policy',RoleName=name+suffix,PolicyName='benchmark-only')
                aws('iam','delete-role',RoleName=name+suffix)
            aws('ec2','delete-security-group',GroupId=s['securityGroup'])
            s.update(phase='cleaned',cleanupVerifiedAt=datetime.now(timezone.utc).isoformat());save(path,s)
    print(json.dumps(s,indent=2))

if __name__=='__main__': main()
