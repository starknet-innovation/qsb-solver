"""Persist one-shot GPU API intents for execution by the AWS MCP transport.

No AWS SDK, CLI, network, or remote execution occurs here. The operator executes
recorded calls once and saves returned receipts. An uncertain call is reconciled,
never replayed. This is an operator planner, not automatic cloud orchestration.
"""
import argparse
import base64
from datetime import datetime, timedelta, timezone
import hashlib
import fcntl
import io
import json
from pathlib import Path
import subprocess
import sys
import uuid
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'ops/aws-gpu-benchmark'))
from launch import boot_script
from operator_config import load_config


def call(service, operation, **params):
    return {'service': service, 'operation': ''.join(part.title() for part in operation.split('_')), 'parameters': params}


def request_hash(request):
    return hashlib.sha256(json.dumps(request, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def policy(statements):
    return json.dumps({'Version': '2012-10-17', 'Statement': statements})


def trust(service):
    return policy([{'Effect': 'Allow', 'Principal': {'Service': service}, 'Action': 'sts:AssumeRole'}])


def epoch_now():
    return int(datetime.now(timezone.utc).timestamp())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prepare(config, commit, caller, token=None):
    require(caller.get('Account') == config['account'], 'Wrong account')
    token = token or str(uuid.uuid4())
    require(str(uuid.UUID(token)) == token, 'Invalid token')
    name = 'qsb-bench-' + token[:8]
    account, region = config['account'], config['region']
    require(region == 'eu-west-1', 'Wrong region')
    function = f'arn:aws:lambda:{region}:{account}:function:{name}'
    cleanup_policy = policy([
        {'Effect': 'Allow', 'Action': 'ec2:DescribeInstances', 'Resource': '*'},
        {'Effect': 'Allow', 'Action': 'ec2:TerminateInstances',
         'Resource': f'arn:aws:ec2:{region}:{account}:instance/*',
         'Condition': {'StringEquals': {'ec2:ResourceTag/QsbBenchmarkToken': token}}}])
    schedule_trust = policy([{'Effect': 'Allow', 'Principal': {'Service': 'scheduler.amazonaws.com'},
        'Action': 'sts:AssumeRole', 'Condition': {'StringEquals': {'aws:SourceAccount': account},
        'ArnEquals': {'aws:SourceArn': f'arn:aws:scheduler:{region}:{account}:schedule-group/default'}}}])
    calls = [
        call('iam', 'create_role', RoleName=name+'-host', AssumeRolePolicyDocument=trust('ec2.amazonaws.com')),
        call('iam', 'put_role_policy', RoleName=name+'-host', PolicyName='benchmark-only',
             PolicyDocument=(ROOT/'ops/aws-gpu-benchmark/instance-policy.json').read_text()),
        call('iam', 'create_instance_profile', InstanceProfileName=name),
        call('iam', 'add_role_to_instance_profile', InstanceProfileName=name, RoleName=name+'-host'),
        call('ec2', 'create_security_group', GroupName=name, Description='Isolated QSB benchmark; no inbound', VpcId=config['vpc']),
        call('iam', 'create_role', RoleName=name+'-cleanup', AssumeRolePolicyDocument=trust('lambda.amazonaws.com')),
        call('iam', 'put_role_policy', RoleName=name+'-cleanup', PolicyName='benchmark-only', PolicyDocument=cleanup_policy),
        call('iam', 'create_role', RoleName=name+'-schedule', AssumeRolePolicyDocument=schedule_trust),
        call('iam', 'put_role_policy', RoleName=name+'-schedule', PolicyName='benchmark-only',
             PolicyDocument=policy([{'Effect': 'Allow', 'Action': 'lambda:InvokeFunction', 'Resource': function}]))]
    return {'schema': 1, 'phase': 'prepare-intent', 'token': token, 'name': name,
            'controllerCommit': commit, 'operatorConfig': config, 'functionArn': function, 'calls': calls}


def bind_prepared(state, receipts):
    require(state['phase'] == 'prepare-intent', 'Wrong phase')
    require(len(receipts) == len(state['calls']), 'All ordered prepare receipts required')
    for planned, receipt in zip(state['calls'], receipts):
        require(isinstance(receipt, dict) and receipt.get('success') is True and
                receipt.get('operation') == planned['operation'] and
                receipt.get('requestSha256') == request_hash(planned) and
                isinstance(receipt.get('result'), dict), 'Successful bound prepare receipts required')
    group = receipts[4]['result'].get('GroupId', '')
    require(group.startswith('sg-'), 'Missing security group')
    state.update(phase='prepared', securityGroup=group, prepareReceipts=receipts)
    return state


def arm(state, now):
    require(state['phase'] == 'prepared', 'Already armed or prepare incomplete')
    deadline = now + 25*60
    archive = io.BytesIO()
    with zipfile.ZipFile(archive, 'w') as z:
        z.writestr('cleanup.py', (HERE/'cleanup.py').read_bytes())
    data = archive.getvalue()
    config, name = state['operatorConfig'], state['name']
    expected = {'Name': name, 'GroupName': 'default',
        'ScheduleExpression': f"at({datetime.fromtimestamp(deadline, timezone.utc).replace(second=0)+timedelta(minutes=1):%Y-%m-%dT%H:%M:%S})",
        'ScheduleExpressionTimezone': 'UTC', 'FlexibleTimeWindow': {'Mode': 'OFF'},
        'State': 'ENABLED', 'ActionAfterCompletion': 'DELETE',
        'Target': {'Arn': state['functionArn'], 'RoleArn': f"arn:aws:iam::{config['account']}:role/{name}-schedule",
                   'Input': '{}', 'RetryPolicy': {'MaximumEventAgeInSeconds': 300, 'MaximumRetryAttempts': 3}}}
    state.update(phase='arm-intent', deadline=deadline, schedule=expected,
                 cleanupZipBase64=base64.b64encode(data).decode(),
                 cleanupCodeSha256=base64.b64encode(hashlib.sha256(data).digest()).decode(),
                 calls=[call('lambda', 'create_function', FunctionName=name, Runtime='python3.12',
                    Role=f"arn:aws:iam::{config['account']}:role/{name}-cleanup", Handler='cleanup.handler', Timeout=60,
                    Environment={'Variables': {'RUN_TOKEN': state['token'], 'DEADLINE': str(deadline)}},
                    Code={'ZipFile': base64.b64encode(data).decode()}),
                    call('scheduler', 'create_schedule', **expected)])
    # ZipFile is base64 transport representation: MCP must decode it to SDK bytes.
    state['transportNotes'] = ['Code.ZipFile is base64; decode to bytes at SDK boundary.',
        'Wait for Lambda Active and verify CodeSha256 before creating Scheduler.',
        'Read back the exact schedule before launch. Never extend this deadline.']
    return state


def launch(state, evidence, now):
    require(state['phase'] == 'arm-intent', 'Launch intent already exists or wrong phase')
    require(state['deadline'] - now >= 20*60, 'Insufficient time')
    config, name = state['operatorConfig'], state['name']
    require(evidence['caller']['Account'] == config['account'], 'Wrong account')
    lam = evidence['lambda']
    require(lam['State'] == 'Active' and lam['CodeSha256'] == state['cleanupCodeSha256'] and
            lam['FunctionArn'] == state['functionArn'] and lam['Runtime'] == 'python3.12' and
            lam['Handler'] == 'cleanup.handler' and lam['Timeout'] == 60 and
            lam['Role'] == f"arn:aws:iam::{config['account']}:role/{name}-cleanup" and
            lam['Environment']['Variables'] == {'RUN_TOKEN': state['token'], 'DEADLINE': str(state['deadline'])}, 'Cleanup Lambda mismatch')
    require(all(evidence['schedule'].get(k) == v for k, v in state['schedule'].items()), 'Schedule mismatch')
    require(evidence['quota']['Quota']['Value'] >= 4, 'Quota insufficient')
    require(not evidence['instances']['Reservations'], 'Existing token instance; reconcile')
    require(not evidence['activeGpus']['Reservations'], 'Other GPU capacity active')
    images = evidence['images']['Images']
    require(len(images) == 1, 'One AMI required')
    image = images[0]
    require(image['ImageId'] == config['ami'] and image['Architecture'] == 'x86_64' and
            image['OwnerId'] == '898082745236' and image['RootDeviceType'] == 'ebs', 'AMI mismatch')
    mappings = image['BlockDeviceMappings']
    roots = [m for m in mappings if 'Ebs' in m]
    require(len(roots) == 1 and roots[0]['DeviceName'] == image['RootDeviceName'] and
            all(m is roots[0] or (set(m) == {'DeviceName', 'VirtualName'} and
                m['VirtualName'] in ('ephemeral0', 'ephemeral1')) for m in mappings), 'AMI mapping mismatch')
    groups = evidence['groups']['SecurityGroups']
    require(len(groups) == 1 and groups[0]['GroupId'] == state['securityGroup'] and
            groups[0]['VpcId'] == config['vpc'] and not groups[0]['IpPermissions'], 'Security group mismatch')
    require(now - evidence['observedAt'] in range(61), 'Stale preflight')
    start = datetime.fromtimestamp(state['deadline'], timezone.utc)-timedelta(minutes=55)
    request = dict(ImageId=config['ami'], InstanceType='g5.xlarge', MinCount=1, MaxCount=1,
        ClientToken=state['token'], SubnetId=config['subnet'], SecurityGroupIds=[state['securityGroup']],
        IamInstanceProfile={'Name': name}, InstanceInitiatedShutdownBehavior='terminate', DisableApiTermination=False,
        MetadataOptions={'HttpTokens': 'required', 'HttpPutResponseHopLimit': 1}, UserData=boot_script(start),
        BlockDeviceMappings=[{'DeviceName': image['RootDeviceName'], 'Ebs': {'VolumeSize': 80,
            'VolumeType': 'gp3', 'Encrypted': True, 'DeleteOnTermination': True}}],
        TagSpecifications=[{'ResourceType': 'instance', 'Tags': [{'Key': 'Name', 'Value': name},
            {'Key': 'QsbBenchmarkToken', 'Value': state['token']}, {'Key': 'SourceCommit', 'Value': state['controllerCommit']}]}])
    state.update(phase='launch-intent', preflight=evidence, calls=[call('ec2', 'run_instances', **request)])
    return state


def cleanup_inventory(state):
    """Read-only inventory, including detached root volumes. No success inference."""
    config, name = state['operatorConfig'], state['name']
    return [call('ec2', 'describe_instances', Filters=[{'Name': 'tag:QsbBenchmarkToken', 'Values': [state['token']]}]),
            *[call('ec2', 'describe_volumes', Filters=[{'Name': 'volume-id', 'Values': [v]}]) for v in state.get('volumeIds', [])],
            call('scheduler', 'list_schedules', NamePrefix=name),
            call('lambda', 'list_functions'), call('iam', 'get_instance_profile', InstanceProfileName=name),
            *[call('iam', 'get_role', RoleName=name+s) for s in ['-host', '-cleanup', '-schedule']],
            call('ec2', 'describe_security_groups', Filters=[{'Name': 'group-name', 'Values': [name]},
                                                           {'Name': 'vpc-id', 'Values': [config['vpc']]}])]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['prepare', 'prepared', 'arm', 'launch', 'cleanup-inventory'])
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--evidence', type=Path)
    args = parser.parse_args()
    args.state.parent.mkdir(parents=True, exist_ok=True)
    lock = args.state.with_suffix(args.state.suffix + '.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    config = load_config()
    require(not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT), 'Dirty checkout')
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    require(commit == subprocess.check_output(['git', 'rev-parse', '@{upstream}'], cwd=ROOT, text=True).strip(), 'Source not pushed')
    require(ROOT not in args.state.resolve().parents, 'State must be outside checkout')
    evidence = json.loads(args.evidence.read_text()) if args.evidence else None
    if args.phase == 'prepare':
        require(not args.state.exists(), 'Existing state; reconcile')
        state = prepare(config, commit, evidence)
        args.state.parent.mkdir(parents=True, exist_ok=True)
        with args.state.open('x') as out:
            json.dump(state, out, indent=2)
    else:
        state = json.loads(args.state.read_text())
        require(state['operatorConfig'] == config and state['controllerCommit'] == commit, 'Source or operator scope changed')
        if args.phase == 'cleanup-inventory':
            print(json.dumps(cleanup_inventory(state), indent=2)); return
        if args.phase == 'prepared': state = bind_prepared(state, evidence)
        elif args.phase == 'arm': state = arm(state, epoch_now())
        elif args.phase == 'launch': state = launch(state, evidence, epoch_now())
        tmp = args.state.with_suffix('.tmp')
        tmp.write_text(json.dumps(state, indent=2)+'\n'); tmp.replace(args.state)
    print(json.dumps(state, indent=2))


if __name__ == '__main__':
    main()
