"""Independent fixed-deadline Batch shutdown. Leaves evidence and IAM for audited collection."""
import os
import time

ACTIVE = ('SUBMITTED', 'PENDING', 'RUNNABLE', 'STARTING', 'RUNNING')


def stop(call, queue, environment, token):
    instances = [i for r in call('ec2', 'describe-instances', Filters=[
        {'Name': 'tag:QsbSolveCampaign', 'Values': [token]}])['Reservations'] for i in r['Instances']]
    volumes = [b['Ebs']['VolumeId'] for i in instances for b in i.get('BlockDeviceMappings', []) if 'Ebs' in b]
    def receipt(value):
        return {**value, 'volumeIds': volumes}
    queues = call('batch', 'describe-job-queues', jobQueues=[queue])['jobQueues']
    environments = call('batch', 'describe-compute-environments', computeEnvironments=[environment])['computeEnvironments']
    changed = False
    if queues and queues[0]['state'] != 'DISABLED':
        call('batch', 'update-job-queue', jobQueue=queue, state='DISABLED')
        changed = True
    if environments and environments[0]['state'] != 'DISABLED':
        call('batch', 'update-compute-environment', computeEnvironment=environment, state='DISABLED')
        changed = True
    jobs = []
    if queues:
        for status in ACTIVE:
            request = {'jobQueue': queue, 'jobStatus': status}
            while True:
                page = call('batch', 'list-jobs', **request)
                jobs += page['jobSummaryList']
                if not page.get('nextToken'):
                    break
                request['nextToken'] = page['nextToken']
    for job in jobs:
        operation = 'terminate-job' if job['status'] in ('STARTING', 'RUNNING') else 'cancel-job'
        call('batch', operation, jobId=job['jobId'], reason='Public synthetic campaign completed or fixed deadline reached')
    if jobs:
        return receipt({'done': False, 'activeJobs': len(jobs)})
    if changed:
        return receipt({'done': False, 'disabling': True})
    if queues:
        queue_state = queues[0]
        if queue_state['status'] != 'VALID':
            return receipt({'done': False, 'queueStatus': queue_state['status']})
        if queue_state.get('computeEnvironmentOrder'):
            call('batch', 'update-job-queue', jobQueue=queue, computeEnvironmentOrder=[])
        else:
            call('batch', 'delete-job-queue', jobQueue=queue)
        return receipt({'done': False, 'queueDeletionPending': True})
    if environments:
        if environments[0]['status'] not in ('DELETING', 'UPDATING', 'CREATING'):
            call('batch', 'delete-compute-environment', computeEnvironment=environment)
        return receipt({'done': False, 'environmentDeletionPending': True})
    active = [i['InstanceId'] for i in instances if i['State']['Name'] != 'terminated']
    if active:
        call('ec2', 'terminate-instances', InstanceIds=active)
    return receipt({'done': not active, 'instanceStates': [i['State']['Name'] for i in instances]})


def handler(event, context):
    import boto3
    from botocore.config import Config
    deadline = int(os.environ['DEADLINE'])
    if time.time() < deadline:
        return {'beforeDeadline': True}
    clients = {name: boto3.client(name, config=Config(connect_timeout=5, read_timeout=20,
                 retries={'total_max_attempts': 1})) for name in ('batch', 'ec2')}
    def call(service, operation, **params):
        return getattr(clients[service], operation.replace('-', '_'))(**params)
    while context.get_remaining_time_in_millis() > 35000:
        result = stop(call, os.environ['QUEUE'], os.environ['COMPUTE_ENVIRONMENT'], os.environ['TOKEN'])
        print(result, flush=True)
        if result['done']:
            return result
        time.sleep(15)
    raise RuntimeError('Independent cleanup incomplete; scheduler must retry and operator must reconcile')
