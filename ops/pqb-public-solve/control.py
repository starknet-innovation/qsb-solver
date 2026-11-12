"""One-shot private Batch validation infrastructure; all configuration/receipts stay outside Git."""
import argparse
import base64
from datetime import datetime, timedelta, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import zipfile

ROOT=Path(__file__).resolve().parents[2]
sys.path.append(str(ROOT/'ops/aws-gpu-execution'))
from mcp_rpc import exchange
from cleanup import stop


def document(statements):return json.dumps({'Version':'2012-10-17','Statement':statements})
def allow(actions,resources):return {'Effect':'Allow','Action':actions,'Resource':resources}
def trust(service):return document([{'Effect':'Allow','Principal':{'Service':service},'Action':'sts:AssumeRole'}])
def save(path,value):
    temp=path.with_suffix('.tmp');temp.write_text(json.dumps(value,indent=2)+'\n');temp.replace(path)


def function_exists(call,name):
    """ListFunctions returns at most 50 per call: follow NextMarker before deciding the function is gone."""
    marker=None
    while True:
        page=call('lambda','list-functions',**({'Marker':marker} if marker else {}))
        if any(f['FunctionName']==name for f in page.get('Functions',[])):return True
        marker=page.get('NextMarker')
        if not marker:return False


NOT_FOUND=('NoSuchEntity','ResourceNotFoundException','RepositoryNotFoundException','NoSuchBucket','NotFound',
           'does not exist','cannot be found','not found')
def delete(call,service,operation,**params):
    """A deletion that may already have happened: removal must be able to resume after a partial run."""
    try:call(service,operation,**params)
    except RuntimeError as error:
        if not any(marker in str(error) for marker in NOT_FOUND):raise


def job_definitions(call,name):
    """Every ACTIVE revision of the campaign's job definition, whether or not the state recorded it."""
    found,token=[],None
    while True:
        page=call('batch','describe-job-definitions',jobDefinitionName=name,status='ACTIVE',**({'nextToken':token} if token else {}))
        found+=[d['jobDefinitionArn'] for d in page.get('jobDefinitions',[])]
        token=page.get('nextToken')
        if not token:return found


def launch_template_ids(call,name,recorded=None):
    """The campaign's launch template as EC2 reports it by name, plus a recorded id it still knows."""
    found=[t['LaunchTemplateId'] for t in call('ec2','describe-launch-templates',Filters=[{'Name':'launch-template-name','Values':[name]}]).get('LaunchTemplates',[])]
    if recorded and recorded not in found and call('ec2','describe-launch-templates',Filters=[{'Name':'launch-template-id','Values':[recorded]}]).get('LaunchTemplates'):
        found.append(recorded)
    return found


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['prepare','publisher-access','arm','batch','stop','remove'])
    p.add_argument('--config',type=Path,required=True);p.add_argument('--state',type=Path,required=True)
    a=p.parse_args();config=json.loads(a.config.read_text());path=a.state
    if ROOT in path.resolve().parents or ROOT in a.config.resolve().parents:raise ValueError('External state required')
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT):raise ValueError('Dirty source')
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    if commit!=subprocess.check_output(['git','rev-parse','@{upstream}'],cwd=ROOT,text=True).strip():raise ValueError('Source not pushed')
    account,region,name,token=(config[k] for k in ('account','region','name','token'))
    if region!='eu-west-1' or not re.fullmatch(r'qsb-pqb-solve-[a-f0-9]{8}',name) or not re.fullmatch(r'[a-f0-9-]{36}',token):raise ValueError('Invalid campaign scope')
    def call(service,operation,**params):return exchange(os.environ['QSB_AWS_MCP_RPC_DIR'],region,service,operation,params)
    if call('sts','get-caller-identity')['Account']!=account:raise ValueError('Wrong account')
    arn=lambda service,resource:f'arn:aws:{service}:{region}:{account}:{resource}'
    rolearn=lambda suffix:f'arn:aws:iam::{account}:role/{name}-{suffix}'
    queue=arn('batch','job-queue/'+name);ce=arn('batch','compute-environment/'+name)
    repo=arn('ecr','repository/'+name);function=arn('lambda','function:'+name)
    if a.mode=='prepare':
        if path.exists():raise ValueError('Existing campaign; reconcile rather than repeat')
        s={'format':'qsb-pqb-batch-infrastructure-v1','sourceCommit':commit,'config':config,'phase':'preparing'}
        path.parent.mkdir(parents=True,exist_ok=True);save(path,s)
        call('s3','create-bucket',Bucket=name,CreateBucketConfiguration={'LocationConstraint':region})
        call('s3','put-public-access-block',Bucket=name,PublicAccessBlockConfiguration={k:True for k in ['BlockPublicAcls','IgnorePublicAcls','BlockPublicPolicy','RestrictPublicBuckets']})
        call('ecr','create-repository',repositoryName=name,imageTagMutability='IMMUTABLE',encryptionConfiguration={'encryptionType':'AES256'},imageScanningConfiguration={'scanOnPush':True})
        s['securityGroup']=call('ec2','create-security-group',GroupName=name,Description='Public synthetic Batch validation; no inbound',VpcId=config['vpc'])['GroupId'];save(path,s)
        def role(suffix,principal,statements):
            assumed=json.loads(trust(principal))
            if principal=='scheduler.amazonaws.com':
                assumed['Statement'][0]['Condition']={'StringEquals':{'aws:SourceAccount':account},
                    'ArnEquals':{'aws:SourceArn':arn('scheduler','schedule-group/default')}}
            call('iam','create-role',RoleName=name+'-'+suffix,AssumeRolePolicyDocument=json.dumps(assumed))
            if statements:call('iam','put-role-policy',RoleName=name+'-'+suffix,PolicyName='validation-only',PolicyDocument=document(statements))
        role('host','ec2.amazonaws.com',[])
        call('iam','attach-role-policy',RoleName=name+'-host',PolicyArn='arn:aws:iam::aws:policy/service-role/AmazonEC2ContainerServiceforEC2Role')
        call('iam','create-instance-profile',InstanceProfileName=name)
        call('iam','add-role-to-instance-profile',InstanceProfileName=name,RoleName=name+'-host')
        role('task','ecs-tasks.amazonaws.com',[
            allow(['s3:GetObject'],f'arn:aws:s3:::{name}/inputs/*'),allow(['s3:PutObject'],f'arn:aws:s3:::{name}/outputs/*')])
        role('execute','ecs-tasks.amazonaws.com',[
            allow(['ecr:GetAuthorizationToken'],'*'),allow(['ecr:BatchGetImage','ecr:GetDownloadUrlForLayer','ecr:BatchCheckLayerAvailability'],repo),
            allow(['logs:CreateLogStream','logs:PutLogEvents'],arn('logs','log-group:/qsb-public-solve/'+name+':*'))])
        role('cleanup','lambda.amazonaws.com',[
            allow(['batch:DescribeJobQueues','batch:DescribeComputeEnvironments','batch:ListJobs','ec2:DescribeInstances'],'*'),
            allow(['batch:CancelJob','batch:TerminateJob'],arn('batch','job/*')),
            allow(['batch:UpdateJobQueue','batch:DeleteJobQueue'],queue),
            allow(['batch:UpdateComputeEnvironment','batch:DeleteComputeEnvironment'],ce),
            {**allow('ec2:TerminateInstances',arn('ec2','instance/*')),'Condition':{'StringEquals':{'ec2:ResourceTag/QsbSolveCampaign':token}}},
            allow(['logs:CreateLogStream','logs:PutLogEvents'],arn('logs','log-group:/aws/lambda/'+name+':*'))])
        role('schedule','scheduler.amazonaws.com',[allow('lambda:InvokeFunction',function)])
        for group in ['/qsb-public-solve/'+name,'/aws/lambda/'+name]:
            call('logs','create-log-group',logGroupName=group)
            call('logs','put-retention-policy',logGroupName=group,retentionInDays=7)
        s.update(phase='prepared',queue=queue,computeEnvironment=ce);save(path,s)
    else:
        s=json.loads(path.read_text())
        if s['config']!=config:raise ValueError('Frozen configuration changed')
        if s['sourceCommit']!=commit:
            if a.mode not in ('stop','remove'):raise ValueError('Source changed')
            subprocess.run(['git','merge-base','--is-ancestor',s['sourceCommit'],commit],cwd=ROOT,check=True)
        if a.mode=='publisher-access':
            publisher=json.loads((path.parent/'publisher/state.json').read_text())
            if publisher['controllerCommit']!=commit or publisher['operatorConfig']['account']!=account or not re.fullmatch(r'qsb-bench-[a-f0-9]{8}',publisher['name']):raise ValueError('Wrong publisher state')
            ssm=json.loads((ROOT/'ops/aws-gpu-benchmark/instance-policy.json').read_text())['Statement'][0]
            # Docker registry push operations are outside SDK static analysis; see AWS ECR push policy.
            ecr=allow(['ecr:BatchCheckLayerAvailability','ecr:InitiateLayerUpload','ecr:UploadLayerPart',
                'ecr:CompleteLayerUpload','ecr:PutImage','ecr:DescribeImages','ecr:BatchGetImage'],repo)
            call('iam','put-role-policy',RoleName=publisher['name']+'-host',PolicyName='benchmark-only',
                PolicyDocument=document([ssm,ecr,allow('ecr:GetAuthorizationToken','*')]))
            s['publisherAccess']={'role':publisher['name']+'-host','repository':repo};save(path,s)
        elif a.mode=='arm':
            if s['phase']!='prepared':raise ValueError('Already armed; never extend a deadline')
            deadline=datetime.now(timezone.utc)+timedelta(hours=6)
            s.update(phase='arming',deadline=int(deadline.timestamp()));save(path,s)
            archive=path.parent/'cleanup.zip'
            with zipfile.ZipFile(archive,'w') as z:z.write(Path(__file__).with_name('cleanup.py'),'cleanup.py')
            actual=call('lambda','create-function',FunctionName=name,Runtime='python3.12',Role=rolearn('cleanup'),
                Handler='cleanup.handler',Timeout=900,Code={'S3Bucket':name,'S3Key':'control/cleanup.zip'},
                Environment={'Variables':{'QUEUE':queue,'COMPUTE_ENVIRONMENT':ce,'TOKEN':token,'DEADLINE':str(s['deadline'])}})
            if actual['CodeSha256']!=base64.b64encode(hashlib.sha256(archive.read_bytes()).digest()).decode():raise ValueError('Cleanup source mismatch')
            end=time.monotonic()+120
            while call('lambda','get-function-configuration',FunctionName=name)['State']!='Active':
                if time.monotonic()>end:raise TimeoutError('Cleanup function not active')
                time.sleep(2)
            schedule={'Name':name,'GroupName':'default','ScheduleExpression':f'at({(deadline+timedelta(minutes=1)).replace(second=0,microsecond=0):%Y-%m-%dT%H:%M:%S})',
                'ScheduleExpressionTimezone':'UTC','FlexibleTimeWindow':{'Mode':'OFF'},'State':'ENABLED','ActionAfterCompletion':'DELETE',
                'Target':{'Arn':function,'RoleArn':rolearn('schedule'),'Input':'{}','RetryPolicy':{'MaximumEventAgeInSeconds':3600,'MaximumRetryAttempts':3}}}
            call('scheduler','create-schedule',**schedule)
            actual=call('scheduler','get-schedule',Name=name,GroupName='default')
            for key,value in schedule.items():
                if actual[key]!=value:raise ValueError('Shutdown schedule mismatch')
            script='#!/bin/bash\nset -eu\nleft=$(( '+str(s['deadline'])+' - $(date -u +%s) ))\nif [ "$left" -le 0 ]; then shutdown -h now; exit; fi\nsystemd-run --unit=qsb-public-solve-expire --on-active="${left}s" /sbin/shutdown -h now\n'
            mime='MIME-Version: 1.0\nContent-Type: multipart/mixed; boundary="QSB"\n\n--QSB\nContent-Type: text/x-shellscript; charset="us-ascii"\n\n'+script+'\n--QSB--\n'
            template=call('ec2','create-launch-template',LaunchTemplateName=name,ClientToken=token,LaunchTemplateData={
                'UserData':base64.b64encode(mime.encode()).decode(),'InstanceInitiatedShutdownBehavior':'terminate',
                'MetadataOptions':{'HttpTokens':'required','HttpPutResponseHopLimit':1},
                'BlockDeviceMappings':[{'DeviceName':'/dev/xvda','Ebs':{'VolumeSize':80,'VolumeType':'gp3','Encrypted':True,'DeleteOnTermination':True}}]})
            s.update(phase='armed',launchTemplateId=template['LaunchTemplate']['LaunchTemplateId'],schedule=schedule);save(path,s)
        elif a.mode=='batch':
            if s['phase']!='armed' or time.time()>s['deadline']-5*3600:raise ValueError('Invalid phase or insufficient fixed deadline')
            schedule=call('scheduler','get-schedule',Name=name,GroupName='default')
            for key,value in s['schedule'].items():
                if schedule[key]!=value:raise ValueError('Shutdown schedule changed')
            image=json.loads((path.parent/'private-image.json').read_text())
            if image['sourceCommit']!=commit or image['binding']['files']['grind']!=config['binarySha256']:raise ValueError('Published private image binding mismatch')
            # Unique resource names/intents are persisted before these mutations by the MCP transport.
            result=call('batch','create-compute-environment',computeEnvironmentName=name,type='MANAGED',state='ENABLED',
                serviceRole=f'arn:aws:iam::{account}:role/aws-service-role/batch.amazonaws.com/AWSServiceRoleForBatch',
                computeResources={'type':'EC2','allocationStrategy':'BEST_FIT','minvCpus':0,'maxvCpus':64,'desiredvCpus':0,
                    'instanceTypes':['g5.xlarge'],'subnets':config['subnets'],'securityGroupIds':[s['securityGroup']],
                    'instanceRole':f'arn:aws:iam::{account}:instance-profile/{name}',
                    'ec2Configuration':[{'imageType':'ECS_AL2023_NVIDIA','imageIdOverride':config['gpuAmi']}],
                    'launchTemplate':{'launchTemplateId':s['launchTemplateId'],'version':'1'},
                    'tags':{'Name':name,'QsbSolveCampaign':token}},tags={'QsbSolveCampaign':token})
            s['batchCreateReceipt']=result;save(path,s)
            end=time.monotonic()+300
            while True:
                actual=call('batch','describe-compute-environments',computeEnvironments=[ce])['computeEnvironments'][0]
                if actual['status']=='VALID':break
                if actual['status']=='INVALID' or time.monotonic()>end:raise ValueError(str(actual))
                time.sleep(3)
            call('batch','create-job-queue',jobQueueName=name,state='ENABLED',priority=1,computeEnvironmentOrder=[{'order':1,'computeEnvironment':ce}],tags={'QsbSolveCampaign':token})
            command=json.loads((ROOT/'ops/pqb-public-solve/consumer-lock.json').read_text())['batchCommand']
            definition=call('batch','register-job-definition',jobDefinitionName=name,type='container',platformCapabilities=['EC2'],
                retryStrategy={'attempts':1},timeout={'attemptDurationSeconds':900},containerProperties={
                    'image':image['image'],'command':command,'jobRoleArn':rolearn('task'),'executionRoleArn':rolearn('execute'),
                    'readonlyRootFilesystem':True,'privileged':False,
                    'resourceRequirements':[{'type':'GPU','value':'1'},{'type':'VCPU','value':'4'},{'type':'MEMORY','value':'8192'}],
                    'environment':[{'name':'QSB_JOB_BUCKET','value':name},{'name':'AWS_DEFAULT_REGION','value':region}],
                    'volumes':[{'name':'temporary','host':{}}],'mountPoints':[{'sourceVolume':'temporary','containerPath':'/tmp','readOnly':False}],
                    'logConfiguration':{'logDriver':'awslogs','options':{'awslogs-group':'/qsb-public-solve/'+name,'awslogs-region':region,'awslogs-stream-prefix':'job'}}},
                tags={'QsbSolveCampaign':token})
            s.update(phase='ready',definition=definition['jobDefinitionArn'],image=image['image']);save(path,s)
        elif a.mode=='stop':
            result=stop(call,queue,ce,token);s['shutdownReadback']=result
            s['volumeIds']=sorted(set(s.get('volumeIds',[])+result.get('volumeIds',[])))
            save(path,s);print(json.dumps(result));return
        elif a.mode=='remove':
            if call('batch','describe-job-queues',jobQueues=[queue])['jobQueues'] or call('batch','describe-compute-environments',computeEnvironments=[ce])['computeEnvironments']:raise ValueError('Batch resources remain')
            for volume in s.get('volumeIds',[]):
                if call('ec2','describe-volumes',Filters=[{'Name':'volume-id','Values':[volume]}])['Volumes']:raise ValueError('Recorded volume remains')
            # Each step tolerates a resource that is already gone, so a removal interrupted part-way can be
            # rerun to the end. Job definitions are found by name: a registration whose response was lost
            # is not in the state.
            for definition in sorted(set(job_definitions(call,name)+([s['definition']] if s.get('definition') else []))):
                delete(call,'batch','deregister-job-definition',jobDefinition=definition)
            if call('scheduler','list-schedules',NamePrefix=name)['Schedules']:delete(call,'scheduler','delete-schedule',Name=name,GroupName='default')
            if function_exists(call,name):delete(call,'lambda','delete-function',FunctionName=name)
            # A failed arm may have created the template without recording its id, or not created it:
            # look it up by its campaign name instead of trusting the state.
            for template in launch_template_ids(call,name,s.get('launchTemplateId')):delete(call,'ec2','delete-launch-template',LaunchTemplateId=template)
            delete(call,'iam','remove-role-from-instance-profile',InstanceProfileName=name,RoleName=name+'-host')
            delete(call,'iam','delete-instance-profile',InstanceProfileName=name)
            delete(call,'iam','detach-role-policy',RoleName=name+'-host',PolicyArn='arn:aws:iam::aws:policy/service-role/AmazonEC2ContainerServiceforEC2Role')
            delete(call,'iam','delete-role',RoleName=name+'-host')
            for suffix in ['task','execute','cleanup','schedule']:
                delete(call,'iam','delete-role-policy',RoleName=name+'-'+suffix,PolicyName='validation-only');delete(call,'iam','delete-role',RoleName=name+'-'+suffix)
            if s.get('securityGroup'):delete(call,'ec2','delete-security-group',GroupId=s['securityGroup'])
            delete(call,'ecr','delete-repository',repositoryName=name,force=True)
            # Evidence objects and logs must already have been collected separately.
            try:remaining=call('s3','list-objects-v2',Bucket=name).get('Contents')
            except RuntimeError as error:
                if 'NoSuchBucket' not in str(error):raise
                remaining=None
            if remaining:raise ValueError('Collect and remove staging/evidence objects first')
            delete(call,'s3','delete-bucket',Bucket=name)
            for group in ['/qsb-public-solve/'+name,'/aws/lambda/'+name]:delete(call,'logs','delete-log-group',logGroupName=group)
            s.update(phase='removed',removedAt=datetime.now(timezone.utc).isoformat());save(path,s)
    print(json.dumps(s,indent=2))


if __name__=='__main__':main()
